%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:06 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 146 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   21
%              Number of atoms          :  328 ( 598 expanded)
%              Number of equality atoms :  129 ( 193 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,(
    sK3 != sK3 ),
    inference(superposition,[],[f48,f143])).

fof(f143,plain,(
    sK3 = k1_funct_1(sK5,sK4) ),
    inference(resolution,[],[f139,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_tarski(X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f63,f60])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f37])).

% (15903)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f139,plain,(
    r2_hidden(k4_tarski(sK4,k1_funct_1(sK5,sK4)),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(resolution,[],[f135,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | r2_hidden(X0,k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ) ),
    inference(resolution,[],[f77,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f77,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK3 != k1_funct_1(sK5,sK4)
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f135,plain,(
    r2_hidden(k4_tarski(sK4,k1_funct_1(sK5,sK4)),sK5) ),
    inference(resolution,[],[f134,f47])).

fof(f47,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) ) ),
    inference(resolution,[],[f130,f102])).

fof(f102,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f99,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))
    | v1_relat_1(sK5) ),
    inference(resolution,[],[f77,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f130,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK5)
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK5,X4)),sK5)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(backward_demodulation,[],[f94,f128])).

fof(f128,plain,(
    sK2 = k1_relat_1(sK5) ),
    inference(resolution,[],[f125,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f125,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK2 = k1_relat_1(sK5) ),
    inference(resolution,[],[f123,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f123,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | sK2 = k1_relat_1(sK5) ),
    inference(resolution,[],[f120,f90])).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f120,plain,
    ( sP1(sK3,sK3,k1_xboole_0)
    | sK2 = k1_relat_1(sK5) ),
    inference(superposition,[],[f91,f106])).

fof(f106,plain,
    ( k1_xboole_0 = k2_tarski(sK3,sK3)
    | sK2 = k1_relat_1(sK5) ),
    inference(resolution,[],[f105,f78])).

fof(f78,plain,(
    v1_funct_2(sK5,sK2,k2_tarski(sK3,sK3)) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f45,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,
    ( ~ v1_funct_2(sK5,sK2,k2_tarski(sK3,sK3))
    | sK2 = k1_relat_1(sK5)
    | k1_xboole_0 = k2_tarski(sK3,sK3) ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f97,plain,(
    k1_relat_1(sK5) = k1_relset_1(sK2,k2_tarski(sK3,sK3),sK5) ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( ~ v1_funct_2(sK5,sK2,k2_tarski(sK3,sK3))
    | k1_xboole_0 = k2_tarski(sK3,sK3)
    | sK2 = k1_relset_1(sK2,k2_tarski(sK3,sK3),sK5) ),
    inference(resolution,[],[f98,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

% (15913)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f98,plain,(
    sP0(sK2,sK5,k2_tarski(sK3,sK3)) ),
    inference(resolution,[],[f77,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f21,f25])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f91,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f94,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK5))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK5,X4)),sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f44,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f51])).

% (15904)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (15927)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:22:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.66/0.57  % (15911)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.66/0.57  % (15901)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.57  % (15919)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.58  % (15914)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.58  % (15900)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.58  % (15901)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  fof(f150,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(trivial_inequality_removal,[],[f149])).
% 1.66/0.58  fof(f149,plain,(
% 1.66/0.58    sK3 != sK3),
% 1.66/0.58    inference(superposition,[],[f48,f143])).
% 1.66/0.58  fof(f143,plain,(
% 1.66/0.58    sK3 = k1_funct_1(sK5,sK4)),
% 1.66/0.58    inference(resolution,[],[f139,f80])).
% 1.66/0.58  fof(f80,plain,(
% 1.66/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_tarski(X3,X3))) | X1 = X3) )),
% 1.66/0.58    inference(definition_unfolding,[],[f63,f60])).
% 1.66/0.58  fof(f60,plain,(
% 1.66/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f3])).
% 1.66/0.58  fof(f3,axiom,(
% 1.66/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.58  fof(f63,plain,(
% 1.66/0.58    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f37])).
% 1.66/0.59  % (15903)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.66/0.59    inference(flattening,[],[f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.66/0.59    inference(nnf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.66/0.59  fof(f139,plain,(
% 1.66/0.59    r2_hidden(k4_tarski(sK4,k1_funct_1(sK5,sK4)),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 1.66/0.59    inference(resolution,[],[f135,f100])).
% 1.66/0.59  fof(f100,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(X0,sK5) | r2_hidden(X0,k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))) )),
% 1.66/0.59    inference(resolution,[],[f77,f52])).
% 1.66/0.59  fof(f52,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.59    inference(ennf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.66/0.59  fof(f77,plain,(
% 1.66/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))))),
% 1.66/0.59    inference(definition_unfolding,[],[f46,f60])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.66/0.59    inference(cnf_transformation,[],[f30])).
% 1.66/0.59  fof(f30,plain,(
% 1.66/0.59    sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f29])).
% 1.66/0.59  fof(f29,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f16,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.66/0.59    inference(flattening,[],[f15])).
% 1.66/0.59  fof(f15,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.66/0.59    inference(ennf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.66/0.59    inference(negated_conjecture,[],[f13])).
% 1.66/0.59  fof(f13,conjecture,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.66/0.59  fof(f135,plain,(
% 1.66/0.59    r2_hidden(k4_tarski(sK4,k1_funct_1(sK5,sK4)),sK5)),
% 1.66/0.59    inference(resolution,[],[f134,f47])).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    r2_hidden(sK4,sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f30])).
% 1.66/0.59  fof(f134,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)) )),
% 1.66/0.59    inference(resolution,[],[f130,f102])).
% 1.66/0.59  fof(f102,plain,(
% 1.66/0.59    v1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f99,f65])).
% 1.66/0.59  fof(f65,plain,(
% 1.66/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.66/0.59  fof(f99,plain,(
% 1.66/0.59    ~v1_relat_1(k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) | v1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f77,f66])).
% 1.66/0.59  fof(f66,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.66/0.59    inference(ennf_transformation,[],[f7])).
% 1.66/0.59  fof(f7,axiom,(
% 1.66/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.66/0.59  fof(f130,plain,(
% 1.66/0.59    ( ! [X4] : (~v1_relat_1(sK5) | r2_hidden(k4_tarski(X4,k1_funct_1(sK5,X4)),sK5) | ~r2_hidden(X4,sK2)) )),
% 1.66/0.59    inference(backward_demodulation,[],[f94,f128])).
% 1.66/0.59  fof(f128,plain,(
% 1.66/0.59    sK2 = k1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f125,f67])).
% 1.66/0.59  fof(f67,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.66/0.59  fof(f125,plain,(
% 1.66/0.59    ~r1_tarski(k1_xboole_0,sK3) | sK2 = k1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f123,f76])).
% 1.66/0.59  fof(f76,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.66/0.59  fof(f123,plain,(
% 1.66/0.59    r2_hidden(sK3,k1_xboole_0) | sK2 = k1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f120,f90])).
% 1.66/0.59  fof(f90,plain,(
% 1.66/0.59    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.66/0.59    inference(equality_resolution,[],[f69])).
% 1.66/0.59  fof(f69,plain,(
% 1.66/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f42])).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).
% 1.66/0.59  fof(f41,plain,(
% 1.66/0.59    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f40,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.66/0.59    inference(rectify,[],[f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.66/0.59    inference(flattening,[],[f38])).
% 1.66/0.59  fof(f38,plain,(
% 1.66/0.59    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.66/0.59    inference(nnf_transformation,[],[f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.66/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.66/0.59  fof(f120,plain,(
% 1.66/0.59    sP1(sK3,sK3,k1_xboole_0) | sK2 = k1_relat_1(sK5)),
% 1.66/0.59    inference(superposition,[],[f91,f106])).
% 1.66/0.59  fof(f106,plain,(
% 1.66/0.59    k1_xboole_0 = k2_tarski(sK3,sK3) | sK2 = k1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f105,f78])).
% 1.66/0.59  fof(f78,plain,(
% 1.66/0.59    v1_funct_2(sK5,sK2,k2_tarski(sK3,sK3))),
% 1.66/0.59    inference(definition_unfolding,[],[f45,f60])).
% 1.66/0.59  fof(f45,plain,(
% 1.66/0.59    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 1.66/0.59    inference(cnf_transformation,[],[f30])).
% 1.66/0.59  fof(f105,plain,(
% 1.66/0.59    ~v1_funct_2(sK5,sK2,k2_tarski(sK3,sK3)) | sK2 = k1_relat_1(sK5) | k1_xboole_0 = k2_tarski(sK3,sK3)),
% 1.66/0.59    inference(forward_demodulation,[],[f101,f97])).
% 1.66/0.59  fof(f97,plain,(
% 1.66/0.59    k1_relat_1(sK5) = k1_relset_1(sK2,k2_tarski(sK3,sK3),sK5)),
% 1.66/0.59    inference(resolution,[],[f77,f61])).
% 1.66/0.59  fof(f61,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.66/0.59  fof(f101,plain,(
% 1.66/0.59    ~v1_funct_2(sK5,sK2,k2_tarski(sK3,sK3)) | k1_xboole_0 = k2_tarski(sK3,sK3) | sK2 = k1_relset_1(sK2,k2_tarski(sK3,sK3),sK5)),
% 1.66/0.59    inference(resolution,[],[f98,f53])).
% 1.66/0.59  fof(f53,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f34])).
% 1.66/0.59  % (15913)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.66/0.59    inference(rectify,[],[f33])).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.66/0.59    inference(nnf_transformation,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.66/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.66/0.59  fof(f98,plain,(
% 1.66/0.59    sP0(sK2,sK5,k2_tarski(sK3,sK3))),
% 1.66/0.59    inference(resolution,[],[f77,f57])).
% 1.66/0.59  fof(f57,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(nnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(definition_folding,[],[f21,f25])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(flattening,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f12])).
% 1.66/0.59  fof(f12,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.66/0.59  fof(f91,plain,(
% 1.66/0.59    ( ! [X0,X1] : (sP1(X1,X0,k2_tarski(X0,X1))) )),
% 1.66/0.59    inference(equality_resolution,[],[f74])).
% 1.66/0.59  fof(f74,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.66/0.59    inference(cnf_transformation,[],[f43])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.66/0.59    inference(nnf_transformation,[],[f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.66/0.59    inference(definition_folding,[],[f2,f27])).
% 1.66/0.59  fof(f2,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.66/0.59  fof(f94,plain,(
% 1.66/0.59    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK5)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK5,X4)),sK5) | ~v1_relat_1(sK5)) )),
% 1.66/0.59    inference(resolution,[],[f44,f82])).
% 1.66/0.59  fof(f82,plain,(
% 1.66/0.59    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.66/0.59    inference(equality_resolution,[],[f51])).
% 1.66/0.59  % (15904)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.66/0.59  % (15927)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.59  fof(f51,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f32])).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(flattening,[],[f31])).
% 1.66/0.59  fof(f31,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(nnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(flattening,[],[f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/0.59    inference(ennf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.66/0.59  fof(f44,plain,(
% 1.66/0.59    v1_funct_1(sK5)),
% 1.66/0.59    inference(cnf_transformation,[],[f30])).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    sK3 != k1_funct_1(sK5,sK4)),
% 1.66/0.59    inference(cnf_transformation,[],[f30])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (15901)------------------------------
% 1.66/0.59  % (15901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (15901)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (15901)Memory used [KB]: 1791
% 1.66/0.59  % (15901)Time elapsed: 0.119 s
% 1.66/0.59  % (15901)------------------------------
% 1.66/0.59  % (15901)------------------------------
% 1.66/0.59  % (15915)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.59  % (15908)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.59  % (15902)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.60  % (15899)Success in time 0.235 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:44 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 755 expanded)
%              Number of leaves         :   24 ( 251 expanded)
%              Depth                    :   20
%              Number of atoms          :  270 (3249 expanded)
%              Number of equality atoms :   31 ( 513 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14387)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f892,plain,(
    $false ),
    inference(subsumption_resolution,[],[f891,f629])).

fof(f629,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f626,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f626,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f73,f556])).

fof(f556,plain,(
    k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f547,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f547,plain,(
    v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f73,f431,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f431,plain,(
    ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f361,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f59,f80_D])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f80_D])).

fof(f80_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f361,plain,(
    sP5(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f73,f341,f80])).

fof(f341,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f268,f285])).

fof(f285,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f268,f70])).

fof(f268,plain,(
    v1_xboole_0(k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f73,f266,f63])).

fof(f266,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f163,f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f175,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f175,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f58,f102])).

fof(f102,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f58,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f160,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(X0,sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f60,f123])).

fof(f123,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f100,f99,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f99,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f56,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f6,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f891,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f887,f285])).

fof(f887,plain,(
    ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f103,f359,f544])).

fof(f544,plain,(
    ! [X12,X11] :
      ( ~ sP6(X12,X11)
      | ~ r1_tarski(k1_relat_1(X12),k1_xboole_0)
      | m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f83,f407])).

fof(f407,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f353,f70])).

fof(f353,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f341,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ sP6(X3,X2) ) ),
    inference(general_splitting,[],[f74,f82_D])).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | sP6(X3,X2) ) ),
    inference(cnf_transformation,[],[f82_D])).

fof(f82_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    <=> ~ sP6(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f359,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f193,f341,f80])).

fof(f193,plain,(
    ~ sP5(sK2) ),
    inference(unit_resulting_resolution,[],[f176,f81])).

fof(f176,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f169,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f169,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f167,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f167,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f117,f101])).

fof(f101,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f56,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f117,plain,(
    ~ v1_xboole_0(k2_relset_1(sK1,sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f70])).

fof(f57,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    sP6(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f56,f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (14395)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (14390)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (14392)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (14372)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (14373)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (14375)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (14386)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (14393)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (14378)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14377)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.18/0.52  % (14378)Refutation not found, incomplete strategy% (14378)------------------------------
% 1.18/0.52  % (14378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (14378)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (14378)Memory used [KB]: 6140
% 1.18/0.52  % (14378)Time elapsed: 0.106 s
% 1.18/0.52  % (14378)------------------------------
% 1.18/0.52  % (14378)------------------------------
% 1.18/0.52  % (14374)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.18/0.52  % (14379)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.18/0.52  % (14374)Refutation not found, incomplete strategy% (14374)------------------------------
% 1.18/0.52  % (14374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (14374)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (14374)Memory used [KB]: 10618
% 1.18/0.52  % (14374)Time elapsed: 0.104 s
% 1.18/0.52  % (14374)------------------------------
% 1.18/0.52  % (14374)------------------------------
% 1.18/0.52  % (14389)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.18/0.52  % (14384)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.18/0.52  % (14388)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.18/0.53  % (14388)Refutation not found, incomplete strategy% (14388)------------------------------
% 1.18/0.53  % (14388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (14381)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.18/0.53  % (14383)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.18/0.53  % (14379)Refutation not found, incomplete strategy% (14379)------------------------------
% 1.18/0.53  % (14379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (14379)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (14379)Memory used [KB]: 10618
% 1.18/0.53  % (14379)Time elapsed: 0.110 s
% 1.18/0.53  % (14379)------------------------------
% 1.18/0.53  % (14379)------------------------------
% 1.18/0.53  % (14389)Refutation found. Thanks to Tanya!
% 1.18/0.53  % SZS status Theorem for theBenchmark
% 1.18/0.53  % SZS output start Proof for theBenchmark
% 1.18/0.53  % (14387)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.18/0.53  fof(f892,plain,(
% 1.18/0.53    $false),
% 1.18/0.53    inference(subsumption_resolution,[],[f891,f629])).
% 1.18/0.53  fof(f629,plain,(
% 1.18/0.53    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f626,f75])).
% 1.18/0.53  fof(f75,plain,(
% 1.18/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f38])).
% 1.18/0.53  fof(f38,plain,(
% 1.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.18/0.53    inference(ennf_transformation,[],[f21])).
% 1.18/0.53  fof(f21,plain,(
% 1.18/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.18/0.53    inference(unused_predicate_definition_removal,[],[f9])).
% 1.18/0.53  fof(f9,axiom,(
% 1.18/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.18/0.53  fof(f626,plain,(
% 1.18/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.18/0.53    inference(superposition,[],[f73,f556])).
% 1.18/0.53  fof(f556,plain,(
% 1.18/0.53    k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f547,f70])).
% 1.18/0.53  fof(f70,plain,(
% 1.18/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f34])).
% 1.18/0.53  fof(f34,plain,(
% 1.18/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.18/0.53    inference(ennf_transformation,[],[f2])).
% 1.18/0.53  fof(f2,axiom,(
% 1.18/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.18/0.53  fof(f547,plain,(
% 1.18/0.53    v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f73,f431,f63])).
% 1.18/0.53  fof(f63,plain,(
% 1.18/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f28])).
% 1.18/0.53  fof(f28,plain,(
% 1.18/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.18/0.53    inference(flattening,[],[f27])).
% 1.18/0.53  fof(f27,plain,(
% 1.18/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.18/0.53    inference(ennf_transformation,[],[f8])).
% 1.18/0.53  fof(f8,axiom,(
% 1.18/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.18/0.53  fof(f431,plain,(
% 1.18/0.53    ( ! [X0] : (~r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))) )),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f361,f81])).
% 1.18/0.53  fof(f81,plain,(
% 1.18/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 1.18/0.53    inference(general_splitting,[],[f59,f80_D])).
% 1.18/0.53  fof(f80,plain,(
% 1.18/0.53    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP5(X1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f80_D])).
% 1.18/0.53  fof(f80_D,plain,(
% 1.18/0.53    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP5(X1)) )),
% 1.18/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.18/0.53  fof(f59,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f25])).
% 1.18/0.53  fof(f25,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.18/0.53    inference(ennf_transformation,[],[f10])).
% 1.18/0.53  fof(f10,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.18/0.53  fof(f361,plain,(
% 1.18/0.53    sP5(sK4(k1_zfmisc_1(k1_xboole_0)))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f73,f341,f80])).
% 1.18/0.53  fof(f341,plain,(
% 1.18/0.53    v1_xboole_0(k1_xboole_0)),
% 1.18/0.53    inference(backward_demodulation,[],[f268,f285])).
% 1.18/0.53  fof(f285,plain,(
% 1.18/0.53    k1_xboole_0 = k1_relat_1(sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f268,f70])).
% 1.18/0.53  fof(f268,plain,(
% 1.18/0.53    v1_xboole_0(k1_relat_1(sK2))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f73,f266,f63])).
% 1.18/0.53  fof(f266,plain,(
% 1.18/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2))) )),
% 1.18/0.53    inference(subsumption_resolution,[],[f163,f182])).
% 1.18/0.53  fof(f182,plain,(
% 1.18/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 1.18/0.53    inference(resolution,[],[f175,f64])).
% 1.18/0.53  fof(f64,plain,(
% 1.18/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f29])).
% 1.18/0.53  fof(f29,plain,(
% 1.18/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.18/0.53    inference(ennf_transformation,[],[f7])).
% 1.18/0.53  fof(f7,axiom,(
% 1.18/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.18/0.53  fof(f175,plain,(
% 1.18/0.53    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relat_1(sK2))) )),
% 1.18/0.53    inference(backward_demodulation,[],[f58,f102])).
% 1.18/0.53  fof(f102,plain,(
% 1.18/0.53    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f56,f67])).
% 1.18/0.53  fof(f67,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f30])).
% 1.18/0.53  fof(f30,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f16])).
% 1.18/0.53  fof(f16,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.18/0.53  fof(f56,plain,(
% 1.18/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.18/0.53    inference(cnf_transformation,[],[f45])).
% 1.18/0.53  fof(f45,plain,(
% 1.18/0.53    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44,f43,f42])).
% 1.18/0.53  fof(f42,plain,(
% 1.18/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.18/0.53    introduced(choice_axiom,[])).
% 1.18/0.53  fof(f43,plain,(
% 1.18/0.53    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 1.18/0.53    introduced(choice_axiom,[])).
% 1.18/0.53  fof(f44,plain,(
% 1.18/0.53    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.18/0.53    introduced(choice_axiom,[])).
% 1.18/0.53  fof(f24,plain,(
% 1.18/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.18/0.53    inference(flattening,[],[f23])).
% 1.18/0.53  fof(f23,plain,(
% 1.18/0.53    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.18/0.53    inference(ennf_transformation,[],[f20])).
% 1.18/0.53  fof(f20,negated_conjecture,(
% 1.18/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.18/0.53    inference(negated_conjecture,[],[f19])).
% 1.18/0.53  fof(f19,conjecture,(
% 1.18/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 1.18/0.53  fof(f58,plain,(
% 1.18/0.53    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f45])).
% 1.18/0.53  fof(f163,plain,(
% 1.18/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 1.18/0.53    inference(subsumption_resolution,[],[f160,f100])).
% 1.18/0.53  fof(f100,plain,(
% 1.18/0.53    v1_relat_1(sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f56,f72])).
% 1.18/0.53  fof(f72,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f35])).
% 1.18/0.53  fof(f35,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f14])).
% 1.18/0.53  fof(f14,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.18/0.53  fof(f160,plain,(
% 1.18/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,sK1) | ~v1_relat_1(sK2)) )),
% 1.18/0.53    inference(superposition,[],[f60,f123])).
% 1.18/0.53  fof(f123,plain,(
% 1.18/0.53    sK2 = k7_relat_1(sK2,sK1)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f100,f99,f69])).
% 1.18/0.53  fof(f69,plain,(
% 1.18/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f33])).
% 1.18/0.53  fof(f33,plain,(
% 1.18/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.18/0.53    inference(flattening,[],[f32])).
% 1.18/0.53  fof(f32,plain,(
% 1.18/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.18/0.53    inference(ennf_transformation,[],[f12])).
% 1.18/0.53  fof(f12,axiom,(
% 1.18/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.18/0.53  fof(f99,plain,(
% 1.18/0.53    v4_relat_1(sK2,sK1)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f56,f79])).
% 1.18/0.53  fof(f79,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f41])).
% 1.18/0.53  fof(f41,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f22])).
% 1.18/0.53  fof(f22,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.18/0.53    inference(pure_predicate_removal,[],[f15])).
% 1.18/0.53  fof(f15,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.18/0.53  fof(f60,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f47])).
% 1.18/0.53  fof(f47,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.18/0.53    inference(flattening,[],[f46])).
% 1.18/0.53  fof(f46,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.18/0.53    inference(nnf_transformation,[],[f26])).
% 1.18/0.53  fof(f26,plain,(
% 1.18/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.18/0.53    inference(ennf_transformation,[],[f13])).
% 1.18/0.53  fof(f13,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 1.18/0.53  fof(f73,plain,(
% 1.18/0.53    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f53])).
% 1.18/0.53  fof(f53,plain,(
% 1.18/0.53    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 1.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f6,f52])).
% 1.18/0.53  fof(f52,plain,(
% 1.18/0.53    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 1.18/0.53    introduced(choice_axiom,[])).
% 1.18/0.53  fof(f6,axiom,(
% 1.18/0.53    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.18/0.53  fof(f891,plain,(
% 1.18/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.18/0.53    inference(forward_demodulation,[],[f887,f285])).
% 1.18/0.53  fof(f887,plain,(
% 1.18/0.53    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f103,f359,f544])).
% 1.18/0.53  fof(f544,plain,(
% 1.18/0.53    ( ! [X12,X11] : (~sP6(X12,X11) | ~r1_tarski(k1_relat_1(X12),k1_xboole_0) | m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0))) )),
% 1.18/0.53    inference(superposition,[],[f83,f407])).
% 1.18/0.53  fof(f407,plain,(
% 1.18/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f353,f70])).
% 1.18/0.53  fof(f353,plain,(
% 1.18/0.53    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f341,f77])).
% 1.18/0.53  fof(f77,plain,(
% 1.18/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f39])).
% 1.18/0.53  fof(f39,plain,(
% 1.18/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.18/0.53    inference(ennf_transformation,[],[f3])).
% 1.18/0.53  fof(f3,axiom,(
% 1.18/0.53    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.18/0.53  fof(f83,plain,(
% 1.18/0.53    ( ! [X2,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~sP6(X3,X2)) )),
% 1.18/0.53    inference(general_splitting,[],[f74,f82_D])).
% 1.18/0.53  fof(f82,plain,(
% 1.18/0.53    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | sP6(X3,X2)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f82_D])).
% 1.18/0.53  fof(f82_D,plain,(
% 1.18/0.53    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) <=> ~sP6(X3,X2)) )),
% 1.18/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.18/0.53  fof(f74,plain,(
% 1.18/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f37])).
% 1.18/0.53  fof(f37,plain,(
% 1.18/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.18/0.53    inference(flattening,[],[f36])).
% 1.18/0.53  fof(f36,plain,(
% 1.18/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.18/0.53    inference(ennf_transformation,[],[f18])).
% 1.18/0.53  fof(f18,axiom,(
% 1.18/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 1.18/0.53  fof(f359,plain,(
% 1.18/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f193,f341,f80])).
% 1.18/0.53  fof(f193,plain,(
% 1.18/0.53    ~sP5(sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f176,f81])).
% 1.18/0.53  fof(f176,plain,(
% 1.18/0.53    r2_hidden(sK3(sK2),sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f169,f66])).
% 1.18/0.53  fof(f66,plain,(
% 1.18/0.53    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f51])).
% 1.18/0.53  fof(f51,plain,(
% 1.18/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 1.18/0.53  fof(f50,plain,(
% 1.18/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.18/0.53    introduced(choice_axiom,[])).
% 1.18/0.53  fof(f49,plain,(
% 1.18/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.18/0.53    inference(rectify,[],[f48])).
% 1.18/0.53  fof(f48,plain,(
% 1.18/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.18/0.53    inference(nnf_transformation,[],[f1])).
% 1.18/0.53  fof(f1,axiom,(
% 1.18/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.18/0.53  fof(f169,plain,(
% 1.18/0.53    ~v1_xboole_0(sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f167,f78])).
% 1.18/0.53  fof(f78,plain,(
% 1.18/0.53    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f40])).
% 1.18/0.53  fof(f40,plain,(
% 1.18/0.53    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.18/0.53    inference(ennf_transformation,[],[f11])).
% 1.18/0.53  fof(f11,axiom,(
% 1.18/0.53    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 1.18/0.53  fof(f167,plain,(
% 1.18/0.53    ~v1_xboole_0(k2_relat_1(sK2))),
% 1.18/0.53    inference(backward_demodulation,[],[f117,f101])).
% 1.18/0.53  fof(f101,plain,(
% 1.18/0.53    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f56,f68])).
% 1.18/0.53  fof(f68,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f31])).
% 1.18/0.53  fof(f31,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f17])).
% 1.18/0.53  fof(f17,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.18/0.53  fof(f117,plain,(
% 1.18/0.53    ~v1_xboole_0(k2_relset_1(sK1,sK0,sK2))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f57,f70])).
% 1.18/0.53  fof(f57,plain,(
% 1.18/0.53    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 1.18/0.53    inference(cnf_transformation,[],[f45])).
% 1.18/0.53  fof(f103,plain,(
% 1.18/0.53    sP6(sK2,sK0)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f56,f82])).
% 1.18/0.53  % SZS output end Proof for theBenchmark
% 1.18/0.53  % (14389)------------------------------
% 1.18/0.53  % (14389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (14389)Termination reason: Refutation
% 1.18/0.53  
% 1.18/0.53  % (14389)Memory used [KB]: 1791
% 1.18/0.53  % (14389)Time elapsed: 0.125 s
% 1.18/0.53  % (14389)------------------------------
% 1.18/0.53  % (14389)------------------------------
% 1.36/0.53  % (14392)Refutation not found, incomplete strategy% (14392)------------------------------
% 1.36/0.53  % (14392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (14392)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (14392)Memory used [KB]: 6140
% 1.36/0.53  % (14392)Time elapsed: 0.127 s
% 1.36/0.53  % (14392)------------------------------
% 1.36/0.53  % (14392)------------------------------
% 1.36/0.53  % (14380)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.36/0.54  % (14371)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.36/0.54  % (14363)Success in time 0.168 s
%------------------------------------------------------------------------------

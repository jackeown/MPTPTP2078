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
% DateTime   : Thu Dec  3 13:03:59 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 857 expanded)
%              Number of leaves         :   20 ( 207 expanded)
%              Depth                    :   35
%              Number of atoms          :  376 (3406 expanded)
%              Number of equality atoms :   95 ( 659 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(subsumption_resolution,[],[f372,f101])).

fof(f101,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f68,f65])).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (17940)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f68,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f372,plain,(
    v1_xboole_0(k1_tarski(sK0)) ),
    inference(resolution,[],[f362,f104])).

fof(f104,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f70,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f362,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f360,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f360,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X2,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f352,f181])).

fof(f181,plain,(
    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f59,f179])).

fof(f179,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f178,f105])).

fof(f105,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f178,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f177,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f173,f163])).

fof(f163,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f162,f105])).

fof(f162,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f108])).

fof(f108,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f76,f60])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f161,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f58])).

fof(f158,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f173,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f138,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f138,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f137,f105])).

fof(f137,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f66,f130])).

fof(f130,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f127,f105])).

fof(f127,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | sK0 = sK3(sK2) ),
    inference(resolution,[],[f66,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(resolution,[],[f90,f111])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f71,f60])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f59,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f352,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_2(k1_xboole_0,X2,X3)
      | k1_xboole_0 = X3
      | ~ r2_hidden(X4,X2) ) ),
    inference(trivial_inequality_removal,[],[f351])).

fof(f351,plain,(
    ! [X4,X2,X3] :
      ( X2 != X2
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X3
      | ~ v1_funct_2(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f324,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
      | k1_xboole_0 = X1
      | ~ v1_funct_2(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f77,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f324,plain,(
    ! [X2,X3,X1] :
      ( k1_relset_1(X2,X3,k1_xboole_0) != X2
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f321,f64])).

fof(f321,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X2)
      | k1_relset_1(X2,X3,k1_xboole_0) != X2
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f315,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK7(X1,X2),X6),X2)
            & r2_hidden(sK7(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f50,f52,f51])).

fof(f51,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK7(X1,X2),X6),X2)
        & r2_hidden(sK7(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f315,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(resolution,[],[f310,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f71,f64])).

fof(f310,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f309,f106])).

fof(f106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f75,f64])).

fof(f309,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f308,f180])).

fof(f180,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f58,f179])).

fof(f308,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f307,f257])).

fof(f257,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(resolution,[],[f112,f199])).

fof(f199,plain,(
    ~ r2_hidden(sK0,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f163,f179])).

fof(f307,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f98,f280])).

fof(f280,plain,(
    ! [X0] :
      ( sK0 = k4_tarski(X0,k1_funct_1(k1_xboole_0,X0))
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f279,f106])).

fof(f279,plain,(
    ! [X0] :
      ( sK0 = k4_tarski(X0,k1_funct_1(k1_xboole_0,X0))
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f275,f180])).

fof(f275,plain,(
    ! [X0] :
      ( sK0 = k4_tarski(X0,k1_funct_1(k1_xboole_0,X0))
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f248,f98])).

fof(f248,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | sK0 = X2 ) ),
    inference(resolution,[],[f112,f195])).

fof(f195,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(k1_xboole_0))
      | sK0 = X7 ) ),
    inference(backward_demodulation,[],[f155,f179])).

fof(f155,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | sK0 = X7 ) ),
    inference(subsumption_resolution,[],[f154,f105])).

fof(f154,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | sK0 = X7 ) ),
    inference(subsumption_resolution,[],[f146,f58])).

% (17952)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f146,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | sK0 = X7 ) ),
    inference(resolution,[],[f98,f119])).

fof(f98,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.41/0.55  % (17955)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.55  % (17947)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.56  % (17933)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.41/0.56  % (17939)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.57  % (17943)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.57  % (17935)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.58  % (17945)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.58  % (17949)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.58  % (17937)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.58  % (17944)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.58  % (17932)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.58  % (17941)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.55/0.59  % (17941)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % (17934)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.60  % (17938)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.60  % (17949)Refutation not found, incomplete strategy% (17949)------------------------------
% 1.55/0.60  % (17949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (17949)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (17949)Memory used [KB]: 1791
% 1.55/0.60  % (17949)Time elapsed: 0.161 s
% 1.55/0.60  % (17949)------------------------------
% 1.55/0.60  % (17949)------------------------------
% 1.55/0.60  % (17960)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.60  % (17936)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.60  % SZS output start Proof for theBenchmark
% 1.55/0.60  fof(f378,plain,(
% 1.55/0.60    $false),
% 1.55/0.60    inference(subsumption_resolution,[],[f372,f101])).
% 1.55/0.60  fof(f101,plain,(
% 1.55/0.60    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.55/0.60    inference(superposition,[],[f68,f65])).
% 1.55/0.60  fof(f65,plain,(
% 1.55/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.55/0.61  % (17940)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.55/0.61  fof(f68,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f5])).
% 1.55/0.61  fof(f5,axiom,(
% 1.55/0.61    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 1.55/0.61  fof(f372,plain,(
% 1.55/0.61    v1_xboole_0(k1_tarski(sK0))),
% 1.55/0.61    inference(resolution,[],[f362,f104])).
% 1.55/0.61  fof(f104,plain,(
% 1.55/0.61    ( ! [X1] : (r2_hidden(sK5(X1),X1) | v1_xboole_0(X1)) )),
% 1.55/0.61    inference(resolution,[],[f70,f67])).
% 1.55/0.61  fof(f67,plain,(
% 1.55/0.61    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f47])).
% 1.55/0.61  fof(f47,plain,(
% 1.55/0.61    ! [X0] : m1_subset_1(sK5(X0),X0)),
% 1.55/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f46])).
% 1.55/0.61  fof(f46,plain,(
% 1.55/0.61    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK5(X0),X0))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f7,axiom,(
% 1.55/0.61    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.55/0.61  fof(f70,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f28])).
% 1.55/0.61  fof(f28,plain,(
% 1.55/0.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.55/0.61    inference(flattening,[],[f27])).
% 1.55/0.61  fof(f27,plain,(
% 1.55/0.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f10])).
% 1.55/0.61  fof(f10,axiom,(
% 1.55/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.55/0.61  fof(f362,plain,(
% 1.55/0.61    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK0))) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f360,f61])).
% 1.55/0.61  fof(f61,plain,(
% 1.55/0.61    k1_xboole_0 != sK1),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f43,plain,(
% 1.55/0.61    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.55/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f42])).
% 1.55/0.61  fof(f42,plain,(
% 1.55/0.61    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f24,plain,(
% 1.55/0.61    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.55/0.61    inference(flattening,[],[f23])).
% 1.55/0.61  fof(f23,plain,(
% 1.55/0.61    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.55/0.61    inference(ennf_transformation,[],[f21])).
% 1.55/0.61  fof(f21,negated_conjecture,(
% 1.55/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.55/0.61    inference(negated_conjecture,[],[f20])).
% 1.55/0.61  fof(f20,conjecture,(
% 1.55/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.55/0.61  fof(f360,plain,(
% 1.55/0.61    ( ! [X2] : (k1_xboole_0 = sK1 | ~r2_hidden(X2,k1_tarski(sK0))) )),
% 1.55/0.61    inference(resolution,[],[f352,f181])).
% 1.55/0.61  fof(f181,plain,(
% 1.55/0.61    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)),
% 1.55/0.61    inference(backward_demodulation,[],[f59,f179])).
% 1.55/0.61  fof(f179,plain,(
% 1.55/0.61    k1_xboole_0 = sK2),
% 1.55/0.61    inference(subsumption_resolution,[],[f178,f105])).
% 1.55/0.61  fof(f105,plain,(
% 1.55/0.61    v1_relat_1(sK2)),
% 1.55/0.61    inference(resolution,[],[f75,f60])).
% 1.55/0.61  fof(f60,plain,(
% 1.55/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f75,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f33])).
% 1.55/0.61  fof(f33,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(ennf_transformation,[],[f16])).
% 1.55/0.61  fof(f16,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.55/0.61  fof(f178,plain,(
% 1.55/0.61    k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(subsumption_resolution,[],[f177,f58])).
% 1.55/0.61  fof(f58,plain,(
% 1.55/0.61    v1_funct_1(sK2)),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f177,plain,(
% 1.55/0.61    k1_xboole_0 = sK2 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(subsumption_resolution,[],[f173,f163])).
% 1.55/0.61  fof(f163,plain,(
% 1.55/0.61    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 1.55/0.61    inference(subsumption_resolution,[],[f162,f105])).
% 1.55/0.61  fof(f162,plain,(
% 1.55/0.61    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(subsumption_resolution,[],[f161,f108])).
% 1.55/0.61  fof(f108,plain,(
% 1.55/0.61    v5_relat_1(sK2,sK1)),
% 1.55/0.61    inference(resolution,[],[f76,f60])).
% 1.55/0.61  fof(f76,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f34])).
% 1.55/0.61  fof(f34,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(ennf_transformation,[],[f22])).
% 1.55/0.61  fof(f22,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.55/0.61    inference(pure_predicate_removal,[],[f17])).
% 1.55/0.61  fof(f17,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.55/0.61  fof(f161,plain,(
% 1.55/0.61    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(subsumption_resolution,[],[f158,f58])).
% 1.55/0.61  fof(f158,plain,(
% 1.55/0.61    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(resolution,[],[f72,f62])).
% 1.55/0.61  fof(f62,plain,(
% 1.55/0.61    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f72,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f31])).
% 1.55/0.61  fof(f31,plain,(
% 1.55/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.55/0.61    inference(flattening,[],[f30])).
% 1.55/0.61  fof(f30,plain,(
% 1.55/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.55/0.61    inference(ennf_transformation,[],[f13])).
% 1.55/0.61  fof(f13,axiom,(
% 1.55/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.55/0.61  fof(f173,plain,(
% 1.55/0.61    k1_xboole_0 = sK2 | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(resolution,[],[f138,f86])).
% 1.55/0.61  fof(f86,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f55])).
% 1.55/0.61  fof(f55,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.55/0.61    inference(flattening,[],[f54])).
% 1.55/0.61  fof(f54,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.55/0.61    inference(nnf_transformation,[],[f39])).
% 1.55/0.61  fof(f39,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.55/0.61    inference(flattening,[],[f38])).
% 1.55/0.61  fof(f38,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.55/0.61    inference(ennf_transformation,[],[f14])).
% 1.55/0.61  fof(f14,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.55/0.61  fof(f138,plain,(
% 1.55/0.61    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.55/0.61    inference(subsumption_resolution,[],[f137,f105])).
% 1.55/0.61  fof(f137,plain,(
% 1.55/0.61    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.55/0.61    inference(duplicate_literal_removal,[],[f136])).
% 1.55/0.61  fof(f136,plain,(
% 1.55/0.61    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.55/0.61    inference(superposition,[],[f66,f130])).
% 1.55/0.61  fof(f130,plain,(
% 1.55/0.61    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 1.55/0.61    inference(subsumption_resolution,[],[f127,f105])).
% 1.55/0.61  fof(f127,plain,(
% 1.55/0.61    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | sK0 = sK3(sK2)),
% 1.55/0.61    inference(resolution,[],[f66,f119])).
% 1.55/0.61  fof(f119,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 1.55/0.61    inference(resolution,[],[f90,f111])).
% 1.55/0.61  fof(f111,plain,(
% 1.55/0.61    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.55/0.61    inference(resolution,[],[f71,f60])).
% 1.55/0.61  fof(f71,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f29])).
% 1.55/0.61  fof(f29,plain,(
% 1.55/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.61    inference(ennf_transformation,[],[f8])).
% 1.55/0.61  fof(f8,axiom,(
% 1.55/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.55/0.61  fof(f90,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 1.55/0.61    inference(cnf_transformation,[],[f57])).
% 1.55/0.61  fof(f57,plain,(
% 1.55/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.55/0.61    inference(flattening,[],[f56])).
% 1.55/0.61  fof(f56,plain,(
% 1.55/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.55/0.61    inference(nnf_transformation,[],[f6])).
% 1.55/0.61  fof(f6,axiom,(
% 1.55/0.61    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.55/0.61  fof(f66,plain,(
% 1.55/0.61    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f45])).
% 1.55/0.61  fof(f45,plain,(
% 1.55/0.61    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | ~v1_relat_1(X0))),
% 1.55/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f44])).
% 1.55/0.61  fof(f44,plain,(
% 1.55/0.61    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f26,plain,(
% 1.55/0.61    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.55/0.61    inference(flattening,[],[f25])).
% 1.55/0.61  fof(f25,plain,(
% 1.55/0.61    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.55/0.61    inference(ennf_transformation,[],[f12])).
% 1.55/0.61  fof(f12,axiom,(
% 1.55/0.61    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 1.55/0.61  fof(f59,plain,(
% 1.55/0.61    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f352,plain,(
% 1.55/0.61    ( ! [X4,X2,X3] : (~v1_funct_2(k1_xboole_0,X2,X3) | k1_xboole_0 = X3 | ~r2_hidden(X4,X2)) )),
% 1.55/0.61    inference(trivial_inequality_removal,[],[f351])).
% 1.55/0.61  fof(f351,plain,(
% 1.55/0.61    ( ! [X4,X2,X3] : (X2 != X2 | ~r2_hidden(X4,X2) | k1_xboole_0 = X3 | ~v1_funct_2(k1_xboole_0,X2,X3)) )),
% 1.55/0.61    inference(superposition,[],[f324,f220])).
% 1.55/0.61  fof(f220,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(k1_xboole_0,X0,X1)) )),
% 1.55/0.61    inference(resolution,[],[f77,f64])).
% 1.55/0.61  fof(f64,plain,(
% 1.55/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f9])).
% 1.55/0.61  fof(f9,axiom,(
% 1.55/0.61    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.55/0.61  fof(f77,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.55/0.61    inference(cnf_transformation,[],[f48])).
% 1.55/0.61  fof(f48,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(nnf_transformation,[],[f36])).
% 1.55/0.61  fof(f36,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(flattening,[],[f35])).
% 1.55/0.61  fof(f35,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(ennf_transformation,[],[f19])).
% 1.55/0.61  fof(f19,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.55/0.61  fof(f324,plain,(
% 1.55/0.61    ( ! [X2,X3,X1] : (k1_relset_1(X2,X3,k1_xboole_0) != X2 | ~r2_hidden(X1,X2)) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f321,f64])).
% 1.55/0.61  fof(f321,plain,(
% 1.55/0.61    ( ! [X2,X3,X1] : (~r2_hidden(X1,X2) | k1_relset_1(X2,X3,k1_xboole_0) != X2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.55/0.61    inference(resolution,[],[f315,f85])).
% 1.55/0.61  fof(f85,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f53])).
% 1.55/0.61  fof(f53,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK7(X1,X2),X6),X2) & r2_hidden(sK7(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.55/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f50,f52,f51])).
% 1.55/0.61  fof(f51,plain,(
% 1.55/0.61    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f52,plain,(
% 1.55/0.61    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK7(X1,X2),X6),X2) & r2_hidden(sK7(X1,X2),X1)))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f50,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.55/0.61    inference(rectify,[],[f49])).
% 1.55/0.61  fof(f49,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.55/0.61    inference(nnf_transformation,[],[f37])).
% 1.55/0.61  fof(f37,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.55/0.61    inference(ennf_transformation,[],[f18])).
% 1.55/0.61  fof(f18,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.55/0.61  fof(f315,plain,(
% 1.55/0.61    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f310,f112])).
% 1.55/0.61  fof(f112,plain,(
% 1.55/0.61    ( ! [X2,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f71,f64])).
% 1.55/0.61  fof(f310,plain,(
% 1.55/0.61    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f309,f106])).
% 1.55/0.61  fof(f106,plain,(
% 1.55/0.61    v1_relat_1(k1_xboole_0)),
% 1.55/0.61    inference(resolution,[],[f75,f64])).
% 1.55/0.61  fof(f309,plain,(
% 1.55/0.61    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f308,f180])).
% 1.55/0.61  fof(f180,plain,(
% 1.55/0.61    v1_funct_1(k1_xboole_0)),
% 1.55/0.61    inference(backward_demodulation,[],[f58,f179])).
% 1.55/0.61  fof(f308,plain,(
% 1.55/0.61    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f307,f257])).
% 1.55/0.61  fof(f257,plain,(
% 1.55/0.61    ~r2_hidden(sK0,k1_xboole_0)),
% 1.55/0.61    inference(resolution,[],[f112,f199])).
% 1.55/0.61  fof(f199,plain,(
% 1.55/0.61    ~r2_hidden(sK0,k1_relat_1(k1_xboole_0))),
% 1.55/0.61    inference(backward_demodulation,[],[f163,f179])).
% 1.55/0.61  fof(f307,plain,(
% 1.55/0.61    ( ! [X0] : (r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.55/0.61    inference(duplicate_literal_removal,[],[f298])).
% 1.55/0.61  fof(f298,plain,(
% 1.55/0.61    ( ! [X0] : (r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.55/0.61    inference(superposition,[],[f98,f280])).
% 1.55/0.61  fof(f280,plain,(
% 1.55/0.61    ( ! [X0] : (sK0 = k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f279,f106])).
% 1.55/0.61  fof(f279,plain,(
% 1.55/0.61    ( ! [X0] : (sK0 = k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f275,f180])).
% 1.55/0.61  fof(f275,plain,(
% 1.55/0.61    ( ! [X0] : (sK0 = k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f248,f98])).
% 1.55/0.61  fof(f248,plain,(
% 1.55/0.61    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | sK0 = X2) )),
% 1.55/0.61    inference(resolution,[],[f112,f195])).
% 1.55/0.61  fof(f195,plain,(
% 1.55/0.61    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(k1_xboole_0)) | sK0 = X7) )),
% 1.55/0.61    inference(backward_demodulation,[],[f155,f179])).
% 1.55/0.61  fof(f155,plain,(
% 1.55/0.61    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | sK0 = X7) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f154,f105])).
% 1.55/0.61  fof(f154,plain,(
% 1.55/0.61    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | sK0 = X7) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f146,f58])).
% 1.55/0.61  % (17952)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.61  fof(f146,plain,(
% 1.55/0.61    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 = X7) )),
% 1.55/0.61    inference(resolution,[],[f98,f119])).
% 1.55/0.61  fof(f98,plain,(
% 1.55/0.61    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.55/0.61    inference(equality_resolution,[],[f88])).
% 1.55/0.61  fof(f88,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f55])).
% 1.55/0.61  % SZS output end Proof for theBenchmark
% 1.55/0.61  % (17941)------------------------------
% 1.55/0.61  % (17941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (17941)Termination reason: Refutation
% 1.55/0.61  
% 1.55/0.61  % (17941)Memory used [KB]: 1918
% 1.55/0.61  % (17941)Time elapsed: 0.160 s
% 1.55/0.61  % (17941)------------------------------
% 1.55/0.61  % (17941)------------------------------
% 1.55/0.61  % (17931)Success in time 0.245 s
%------------------------------------------------------------------------------

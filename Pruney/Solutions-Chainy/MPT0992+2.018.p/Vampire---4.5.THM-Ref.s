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
% DateTime   : Thu Dec  3 13:03:12 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  132 (1664 expanded)
%              Number of leaves         :   18 ( 407 expanded)
%              Depth                    :   25
%              Number of atoms          :  387 (10469 expanded)
%              Number of equality atoms :   92 (2229 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1302,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1297,f707])).

fof(f707,plain,(
    ~ m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(resolution,[],[f698,f214])).

fof(f214,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5)
    | ~ m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(forward_demodulation,[],[f213,f118])).

fof(f118,plain,(
    ! [X0] : k2_partfun1(sK4,sK5,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(subsumption_resolution,[],[f115,f59])).

fof(f59,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
      | ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
      | ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) )
    & ( k1_xboole_0 = sK4
      | k1_xboole_0 != sK5 )
    & r1_tarski(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
        | ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
        | ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) )
      & ( k1_xboole_0 = sK4
        | k1_xboole_0 != sK5 )
      & r1_tarski(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f115,plain,(
    ! [X0] :
      ( k2_partfun1(sK4,sK5,sK7,X0) = k7_relat_1(sK7,X0)
      | ~ v1_funct_1(sK7) ) ),
    inference(resolution,[],[f61,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f61,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f49])).

fof(f213,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5)
    | ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(forward_demodulation,[],[f212,f118])).

fof(f212,plain,
    ( ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
    | ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(subsumption_resolution,[],[f207,f178])).

fof(f178,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK7,X0)) ),
    inference(subsumption_resolution,[],[f177,f59])).

fof(f177,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK7,X0))
      | ~ v1_funct_1(sK7) ) ),
    inference(subsumption_resolution,[],[f175,f61])).

fof(f175,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK7,X0))
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_1(sK7) ) ),
    inference(superposition,[],[f119,f93])).

fof(f119,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK4,sK5,sK7,X1)) ),
    inference(subsumption_resolution,[],[f116,f59])).

fof(f116,plain,(
    ! [X1] :
      ( v1_funct_1(k2_partfun1(sK4,sK5,sK7,X1))
      | ~ v1_funct_1(sK7) ) ),
    inference(resolution,[],[f61,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f207,plain,
    ( ~ v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
    | ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(backward_demodulation,[],[f64,f118])).

fof(f64,plain,
    ( ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
    | ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f698,plain,(
    v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5) ),
    inference(resolution,[],[f692,f62])).

fof(f62,plain,(
    r1_tarski(sK6,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f692,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4)
      | v1_funct_2(k7_relat_1(sK7,X0),X0,sK5) ) ),
    inference(subsumption_resolution,[],[f691,f613])).

fof(f613,plain,(
    k1_xboole_0 != sK5 ),
    inference(subsumption_resolution,[],[f612,f368])).

fof(f368,plain,(
    v1_funct_2(k7_relat_1(sK7,k1_xboole_0),k1_xboole_0,sK5) ),
    inference(superposition,[],[f298,f360])).

fof(f360,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK7,k1_xboole_0)) ),
    inference(resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f124,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_relat_1(sK7))
      | k1_relat_1(k7_relat_1(sK7,X3)) = X3 ) ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f110,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f298,plain,(
    ! [X1] : v1_funct_2(k7_relat_1(sK7,X1),k1_relat_1(k7_relat_1(sK7,X1)),sK5) ),
    inference(resolution,[],[f296,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f296,plain,(
    ! [X0] : sP0(sK5,k7_relat_1(sK7,X0)) ),
    inference(subsumption_resolution,[],[f295,f125])).

fof(f125,plain,(
    ! [X4] : v1_relat_1(k7_relat_1(sK7,X4)) ),
    inference(resolution,[],[f110,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f295,plain,(
    ! [X0] :
      ( sP0(sK5,k7_relat_1(sK7,X0))
      | ~ v1_relat_1(k7_relat_1(sK7,X0)) ) ),
    inference(subsumption_resolution,[],[f291,f178])).

fof(f291,plain,(
    ! [X0] :
      ( sP0(sK5,k7_relat_1(sK7,X0))
      | ~ v1_funct_1(k7_relat_1(sK7,X0))
      | ~ v1_relat_1(k7_relat_1(sK7,X0)) ) ),
    inference(resolution,[],[f274,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f32,f42])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f274,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK7,X0)),sK5) ),
    inference(subsumption_resolution,[],[f273,f125])).

fof(f273,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK7,X0)),sK5)
      | ~ v1_relat_1(k7_relat_1(sK7,X0)) ) ),
    inference(resolution,[],[f261,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f261,plain,(
    ! [X3] : v5_relat_1(k7_relat_1(sK7,X3),sK5) ),
    inference(resolution,[],[f217,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

% (3255)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f217,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK7,X1),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f216,f59])).

fof(f216,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK7,X1),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_1(sK7) ) ),
    inference(subsumption_resolution,[],[f211,f61])).

fof(f211,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK7,X1),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_1(sK7) ) ),
    inference(superposition,[],[f95,f118])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f612,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,k1_xboole_0),k1_xboole_0,sK5)
    | k1_xboole_0 != sK5 ),
    inference(subsumption_resolution,[],[f610,f66])).

fof(f610,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | ~ v1_funct_2(k7_relat_1(sK7,k1_xboole_0),k1_xboole_0,sK5)
    | k1_xboole_0 != sK5 ),
    inference(superposition,[],[f592,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f592,plain,
    ( ~ r1_tarski(sK4,sK6)
    | ~ v1_funct_2(k7_relat_1(sK7,sK4),sK4,sK5) ),
    inference(subsumption_resolution,[],[f227,f217])).

fof(f227,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,sK4),sK4,sK5)
    | ~ m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ r1_tarski(sK4,sK6) ),
    inference(superposition,[],[f214,f106])).

fof(f106,plain,
    ( sK4 = sK6
    | ~ r1_tarski(sK4,sK6) ),
    inference(resolution,[],[f62,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f691,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4)
      | v1_funct_2(k7_relat_1(sK7,X0),X0,sK5)
      | k1_xboole_0 = sK5 ) ),
    inference(superposition,[],[f350,f218])).

fof(f218,plain,
    ( sK4 = k1_relat_1(sK7)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f190,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f190,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f189,f113])).

fof(f113,plain,(
    sP2(sK4,sK7,sK5) ),
    inference(resolution,[],[f61,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f46,f45,f44])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f189,plain,
    ( sK4 = k1_relat_1(sK7)
    | sP1(sK4,sK5)
    | ~ sP2(sK4,sK7,sK5) ),
    inference(subsumption_resolution,[],[f185,f60])).

fof(f60,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f185,plain,
    ( sK4 = k1_relat_1(sK7)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | sP1(sK4,sK5)
    | ~ sP2(sK4,sK7,sK5) ),
    inference(superposition,[],[f111,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f111,plain,(
    k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f350,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK7))
      | v1_funct_2(k7_relat_1(sK7,X0),X0,sK5) ) ),
    inference(subsumption_resolution,[],[f349,f110])).

fof(f349,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK7,X0),X0,sK5)
      | ~ r1_tarski(X0,k1_relat_1(sK7))
      | ~ v1_relat_1(sK7) ) ),
    inference(superposition,[],[f298,f72])).

fof(f1297,plain,(
    m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(superposition,[],[f299,f1003])).

fof(f1003,plain,(
    sK6 = k1_relat_1(k7_relat_1(sK7,sK6)) ),
    inference(resolution,[],[f944,f62])).

fof(f944,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK4)
      | k1_relat_1(k7_relat_1(sK7,X3)) = X3 ) ),
    inference(backward_demodulation,[],[f124,f924])).

fof(f924,plain,(
    sK4 = k1_relat_1(sK7) ),
    inference(forward_demodulation,[],[f923,f640])).

fof(f640,plain,(
    sK4 = k1_relset_1(sK4,k2_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f505,f613])).

fof(f505,plain,
    ( sK4 = k1_relset_1(sK4,k2_relat_1(sK7),sK7)
    | k1_xboole_0 = sK5 ),
    inference(superposition,[],[f466,f218])).

fof(f466,plain,(
    k1_relat_1(sK7) = k1_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) ),
    inference(resolution,[],[f459,f83])).

fof(f459,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) ),
    inference(resolution,[],[f204,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f204,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(sK7),X2)
      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X2))) ) ),
    inference(resolution,[],[f201,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f201,plain,(
    ! [X9] :
      ( sP0(X9,sK7)
      | ~ r1_tarski(k2_relat_1(sK7),X9) ) ),
    inference(subsumption_resolution,[],[f105,f110])).

fof(f105,plain,(
    ! [X9] :
      ( sP0(X9,sK7)
      | ~ r1_tarski(k2_relat_1(sK7),X9)
      | ~ v1_relat_1(sK7) ) ),
    inference(resolution,[],[f59,f78])).

fof(f923,plain,(
    k1_relat_1(sK7) = k1_relset_1(sK4,k2_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f563,f613])).

fof(f563,plain,
    ( k1_xboole_0 = sK5
    | k1_relat_1(sK7) = k1_relset_1(sK4,k2_relat_1(sK7),sK7) ),
    inference(resolution,[],[f473,f83])).

fof(f473,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(sK7))))
    | k1_xboole_0 = sK5 ),
    inference(superposition,[],[f459,f218])).

% (3260)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f299,plain,(
    ! [X2] : m1_subset_1(k7_relat_1(sK7,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK7,X2)),sK5))) ),
    inference(resolution,[],[f296,f77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (729907200)
% 0.21/0.40  ipcrm: permission denied for id (729939996)
% 0.21/0.44  ipcrm: permission denied for id (729972796)
% 0.21/0.49  ipcrm: permission denied for id (730005609)
% 0.42/0.63  % (3253)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.54/0.64  % (3269)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.54/0.66  % (3270)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.54/0.66  % (3262)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.54/0.67  % (3252)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.54/0.67  % (3245)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.60/0.67  % (3254)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.60/0.67  % (3246)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.60/0.68  % (3251)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.60/0.68  % (3266)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.60/0.68  % (3258)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.60/0.68  % (3244)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.60/0.69  % (3249)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.60/0.69  % (3265)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.60/0.69  % (3253)Refutation found. Thanks to Tanya!
% 0.60/0.69  % SZS status Theorem for theBenchmark
% 0.60/0.69  % (3248)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.60/0.69  % SZS output start Proof for theBenchmark
% 0.60/0.69  fof(f1302,plain,(
% 0.60/0.69    $false),
% 0.60/0.69    inference(subsumption_resolution,[],[f1297,f707])).
% 0.60/0.69  fof(f707,plain,(
% 0.60/0.69    ~m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 0.60/0.69    inference(resolution,[],[f698,f214])).
% 0.60/0.69  fof(f214,plain,(
% 0.60/0.69    ~v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5) | ~m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 0.60/0.69    inference(forward_demodulation,[],[f213,f118])).
% 0.60/0.69  fof(f118,plain,(
% 0.60/0.69    ( ! [X0] : (k2_partfun1(sK4,sK5,sK7,X0) = k7_relat_1(sK7,X0)) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f115,f59])).
% 0.60/0.69  fof(f59,plain,(
% 0.60/0.69    v1_funct_1(sK7)),
% 0.60/0.69    inference(cnf_transformation,[],[f49])).
% 0.60/0.69  fof(f49,plain,(
% 0.60/0.69    (~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 0.60/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f48])).
% 0.60/0.69  fof(f48,plain,(
% 0.60/0.69    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.60/0.69    introduced(choice_axiom,[])).
% 0.60/0.69  fof(f24,plain,(
% 0.60/0.69    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.60/0.69    inference(flattening,[],[f23])).
% 0.60/0.69  fof(f23,plain,(
% 0.60/0.69    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.60/0.69    inference(ennf_transformation,[],[f20])).
% 0.60/0.69  fof(f20,negated_conjecture,(
% 0.60/0.69    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.60/0.69    inference(negated_conjecture,[],[f19])).
% 0.60/0.69  fof(f19,conjecture,(
% 0.60/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.60/0.69  fof(f115,plain,(
% 0.60/0.69    ( ! [X0] : (k2_partfun1(sK4,sK5,sK7,X0) = k7_relat_1(sK7,X0) | ~v1_funct_1(sK7)) )),
% 0.60/0.69    inference(resolution,[],[f61,f93])).
% 0.60/0.69  fof(f93,plain,(
% 0.60/0.69    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f39])).
% 0.60/0.69  fof(f39,plain,(
% 0.60/0.69    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.60/0.69    inference(flattening,[],[f38])).
% 0.60/0.69  fof(f38,plain,(
% 0.60/0.69    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.60/0.69    inference(ennf_transformation,[],[f17])).
% 0.60/0.69  fof(f17,axiom,(
% 0.60/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.60/0.69  fof(f61,plain,(
% 0.60/0.69    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.60/0.69    inference(cnf_transformation,[],[f49])).
% 0.60/0.69  fof(f213,plain,(
% 0.60/0.69    ~v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5) | ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 0.60/0.69    inference(forward_demodulation,[],[f212,f118])).
% 0.60/0.69  fof(f212,plain,(
% 0.60/0.69    ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 0.60/0.69    inference(subsumption_resolution,[],[f207,f178])).
% 0.60/0.69  fof(f178,plain,(
% 0.60/0.69    ( ! [X0] : (v1_funct_1(k7_relat_1(sK7,X0))) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f177,f59])).
% 0.60/0.69  fof(f177,plain,(
% 0.60/0.69    ( ! [X0] : (v1_funct_1(k7_relat_1(sK7,X0)) | ~v1_funct_1(sK7)) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f175,f61])).
% 0.60/0.69  fof(f175,plain,(
% 0.60/0.69    ( ! [X0] : (v1_funct_1(k7_relat_1(sK7,X0)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)) )),
% 0.60/0.69    inference(superposition,[],[f119,f93])).
% 0.60/0.69  fof(f119,plain,(
% 0.60/0.69    ( ! [X1] : (v1_funct_1(k2_partfun1(sK4,sK5,sK7,X1))) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f116,f59])).
% 0.60/0.69  fof(f116,plain,(
% 0.60/0.69    ( ! [X1] : (v1_funct_1(k2_partfun1(sK4,sK5,sK7,X1)) | ~v1_funct_1(sK7)) )),
% 0.60/0.69    inference(resolution,[],[f61,f94])).
% 0.60/0.69  fof(f94,plain,(
% 0.60/0.69    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f41])).
% 0.60/0.69  fof(f41,plain,(
% 0.60/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.60/0.69    inference(flattening,[],[f40])).
% 0.60/0.69  fof(f40,plain,(
% 0.60/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.60/0.69    inference(ennf_transformation,[],[f16])).
% 0.60/0.69  fof(f16,axiom,(
% 0.60/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.60/0.69  fof(f207,plain,(
% 0.60/0.69    ~v1_funct_1(k7_relat_1(sK7,sK6)) | ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 0.60/0.69    inference(backward_demodulation,[],[f64,f118])).
% 0.60/0.69  fof(f64,plain,(
% 0.60/0.69    ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))),
% 0.60/0.69    inference(cnf_transformation,[],[f49])).
% 0.60/0.69  fof(f698,plain,(
% 0.60/0.69    v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5)),
% 0.60/0.69    inference(resolution,[],[f692,f62])).
% 0.60/0.69  fof(f62,plain,(
% 0.60/0.69    r1_tarski(sK6,sK4)),
% 0.60/0.69    inference(cnf_transformation,[],[f49])).
% 0.60/0.69  fof(f692,plain,(
% 0.60/0.69    ( ! [X0] : (~r1_tarski(X0,sK4) | v1_funct_2(k7_relat_1(sK7,X0),X0,sK5)) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f691,f613])).
% 0.60/0.69  fof(f613,plain,(
% 0.60/0.69    k1_xboole_0 != sK5),
% 0.60/0.69    inference(subsumption_resolution,[],[f612,f368])).
% 0.60/0.69  fof(f368,plain,(
% 0.60/0.69    v1_funct_2(k7_relat_1(sK7,k1_xboole_0),k1_xboole_0,sK5)),
% 0.60/0.69    inference(superposition,[],[f298,f360])).
% 0.60/0.69  fof(f360,plain,(
% 0.60/0.69    k1_xboole_0 = k1_relat_1(k7_relat_1(sK7,k1_xboole_0))),
% 0.60/0.69    inference(resolution,[],[f124,f66])).
% 0.60/0.69  fof(f66,plain,(
% 0.60/0.69    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f4])).
% 0.60/0.69  fof(f4,axiom,(
% 0.60/0.69    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.60/0.69  fof(f124,plain,(
% 0.60/0.69    ( ! [X3] : (~r1_tarski(X3,k1_relat_1(sK7)) | k1_relat_1(k7_relat_1(sK7,X3)) = X3) )),
% 0.60/0.69    inference(resolution,[],[f110,f72])).
% 0.60/0.69  fof(f72,plain,(
% 0.60/0.69    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f29])).
% 0.60/0.69  fof(f29,plain,(
% 0.60/0.69    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.60/0.69    inference(flattening,[],[f28])).
% 0.60/0.69  fof(f28,plain,(
% 0.60/0.69    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.60/0.69    inference(ennf_transformation,[],[f10])).
% 0.60/0.69  fof(f10,axiom,(
% 0.60/0.69    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.60/0.69  fof(f110,plain,(
% 0.60/0.69    v1_relat_1(sK7)),
% 0.60/0.69    inference(resolution,[],[f61,f82])).
% 0.60/0.69  fof(f82,plain,(
% 0.60/0.69    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.60/0.69    inference(cnf_transformation,[],[f33])).
% 0.60/0.69  fof(f33,plain,(
% 0.60/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.60/0.69    inference(ennf_transformation,[],[f11])).
% 0.60/0.69  fof(f11,axiom,(
% 0.60/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.60/0.69  fof(f298,plain,(
% 0.60/0.69    ( ! [X1] : (v1_funct_2(k7_relat_1(sK7,X1),k1_relat_1(k7_relat_1(sK7,X1)),sK5)) )),
% 0.60/0.69    inference(resolution,[],[f296,f76])).
% 0.60/0.69  fof(f76,plain,(
% 0.60/0.69    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP0(X0,X1)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f51])).
% 0.60/0.69  fof(f51,plain,(
% 0.60/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.60/0.69    inference(nnf_transformation,[],[f42])).
% 0.60/0.69  fof(f42,plain,(
% 0.60/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.60/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.60/0.69  fof(f296,plain,(
% 0.60/0.69    ( ! [X0] : (sP0(sK5,k7_relat_1(sK7,X0))) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f295,f125])).
% 0.60/0.69  fof(f125,plain,(
% 0.60/0.69    ( ! [X4] : (v1_relat_1(k7_relat_1(sK7,X4))) )),
% 0.60/0.69    inference(resolution,[],[f110,f71])).
% 0.60/0.69  fof(f71,plain,(
% 0.60/0.69    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f27])).
% 0.60/0.69  fof(f27,plain,(
% 0.60/0.69    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.60/0.69    inference(ennf_transformation,[],[f8])).
% 0.60/0.69  fof(f8,axiom,(
% 0.60/0.69    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.60/0.69  fof(f295,plain,(
% 0.60/0.69    ( ! [X0] : (sP0(sK5,k7_relat_1(sK7,X0)) | ~v1_relat_1(k7_relat_1(sK7,X0))) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f291,f178])).
% 0.60/0.69  fof(f291,plain,(
% 0.60/0.69    ( ! [X0] : (sP0(sK5,k7_relat_1(sK7,X0)) | ~v1_funct_1(k7_relat_1(sK7,X0)) | ~v1_relat_1(k7_relat_1(sK7,X0))) )),
% 0.60/0.69    inference(resolution,[],[f274,f78])).
% 0.60/0.69  fof(f78,plain,(
% 0.60/0.69    ( ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f43])).
% 0.60/0.69  fof(f43,plain,(
% 0.60/0.69    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.60/0.69    inference(definition_folding,[],[f32,f42])).
% 0.60/0.69  fof(f32,plain,(
% 0.60/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.60/0.69    inference(flattening,[],[f31])).
% 0.60/0.69  fof(f31,plain,(
% 0.60/0.69    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.60/0.69    inference(ennf_transformation,[],[f18])).
% 0.60/0.69  fof(f18,axiom,(
% 0.60/0.69    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.60/0.69  fof(f274,plain,(
% 0.60/0.69    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK7,X0)),sK5)) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f273,f125])).
% 0.60/0.69  fof(f273,plain,(
% 0.60/0.69    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK7,X0)),sK5) | ~v1_relat_1(k7_relat_1(sK7,X0))) )),
% 0.60/0.69    inference(resolution,[],[f261,f73])).
% 0.60/0.69  fof(f73,plain,(
% 0.60/0.69    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f50])).
% 0.60/0.69  fof(f50,plain,(
% 0.60/0.69    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.60/0.69    inference(nnf_transformation,[],[f30])).
% 0.60/0.69  fof(f30,plain,(
% 0.60/0.69    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.60/0.69    inference(ennf_transformation,[],[f7])).
% 0.60/0.69  fof(f7,axiom,(
% 0.60/0.69    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.60/0.69  fof(f261,plain,(
% 0.60/0.69    ( ! [X3] : (v5_relat_1(k7_relat_1(sK7,X3),sK5)) )),
% 0.60/0.69    inference(resolution,[],[f217,f84])).
% 0.60/0.69  fof(f84,plain,(
% 0.60/0.69    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.60/0.69    inference(cnf_transformation,[],[f35])).
% 0.60/0.69  fof(f35,plain,(
% 0.60/0.69    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.60/0.69    inference(ennf_transformation,[],[f21])).
% 0.60/0.69  fof(f21,plain,(
% 0.60/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.60/0.69    inference(pure_predicate_removal,[],[f12])).
% 0.60/0.69  % (3255)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.60/0.69  fof(f12,axiom,(
% 0.60/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.60/0.69  fof(f217,plain,(
% 0.60/0.69    ( ! [X1] : (m1_subset_1(k7_relat_1(sK7,X1),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f216,f59])).
% 0.60/0.69  fof(f216,plain,(
% 0.60/0.69    ( ! [X1] : (m1_subset_1(k7_relat_1(sK7,X1),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)) )),
% 0.60/0.69    inference(subsumption_resolution,[],[f211,f61])).
% 0.60/0.69  fof(f211,plain,(
% 0.60/0.69    ( ! [X1] : (m1_subset_1(k7_relat_1(sK7,X1),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)) )),
% 0.60/0.69    inference(superposition,[],[f95,f118])).
% 0.60/0.69  fof(f95,plain,(
% 0.60/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f41])).
% 0.60/0.69  fof(f612,plain,(
% 0.60/0.69    ~v1_funct_2(k7_relat_1(sK7,k1_xboole_0),k1_xboole_0,sK5) | k1_xboole_0 != sK5),
% 0.60/0.69    inference(subsumption_resolution,[],[f610,f66])).
% 0.60/0.69  fof(f610,plain,(
% 0.60/0.69    ~r1_tarski(k1_xboole_0,sK6) | ~v1_funct_2(k7_relat_1(sK7,k1_xboole_0),k1_xboole_0,sK5) | k1_xboole_0 != sK5),
% 0.60/0.69    inference(superposition,[],[f592,f63])).
% 0.60/0.69  fof(f63,plain,(
% 0.60/0.69    k1_xboole_0 = sK4 | k1_xboole_0 != sK5),
% 0.60/0.69    inference(cnf_transformation,[],[f49])).
% 0.60/0.69  fof(f592,plain,(
% 0.60/0.69    ~r1_tarski(sK4,sK6) | ~v1_funct_2(k7_relat_1(sK7,sK4),sK4,sK5)),
% 0.60/0.69    inference(subsumption_resolution,[],[f227,f217])).
% 0.60/0.69  fof(f227,plain,(
% 0.60/0.69    ~v1_funct_2(k7_relat_1(sK7,sK4),sK4,sK5) | ~m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~r1_tarski(sK4,sK6)),
% 0.60/0.69    inference(superposition,[],[f214,f106])).
% 0.60/0.69  fof(f106,plain,(
% 0.60/0.69    sK4 = sK6 | ~r1_tarski(sK4,sK6)),
% 0.60/0.69    inference(resolution,[],[f62,f81])).
% 0.60/0.69  fof(f81,plain,(
% 0.60/0.69    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f53])).
% 0.60/0.69  fof(f53,plain,(
% 0.60/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.60/0.69    inference(flattening,[],[f52])).
% 0.60/0.69  fof(f52,plain,(
% 0.60/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.60/0.69    inference(nnf_transformation,[],[f3])).
% 0.60/0.69  fof(f3,axiom,(
% 0.60/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.60/0.69  fof(f691,plain,(
% 0.60/0.69    ( ! [X0] : (~r1_tarski(X0,sK4) | v1_funct_2(k7_relat_1(sK7,X0),X0,sK5) | k1_xboole_0 = sK5) )),
% 0.60/0.69    inference(superposition,[],[f350,f218])).
% 0.60/0.69  fof(f218,plain,(
% 0.60/0.69    sK4 = k1_relat_1(sK7) | k1_xboole_0 = sK5),
% 0.60/0.69    inference(resolution,[],[f190,f89])).
% 0.60/0.69  fof(f89,plain,(
% 0.60/0.69    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP1(X0,X1)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f58])).
% 0.60/0.69  fof(f58,plain,(
% 0.60/0.69    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.60/0.69    inference(nnf_transformation,[],[f44])).
% 0.60/0.69  fof(f44,plain,(
% 0.60/0.69    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.60/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.60/0.69  fof(f190,plain,(
% 0.60/0.69    sP1(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 0.60/0.69    inference(subsumption_resolution,[],[f189,f113])).
% 0.60/0.69  fof(f113,plain,(
% 0.60/0.69    sP2(sK4,sK7,sK5)),
% 0.60/0.69    inference(resolution,[],[f61,f91])).
% 0.60/0.69  fof(f91,plain,(
% 0.60/0.69    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.60/0.69    inference(cnf_transformation,[],[f47])).
% 0.60/0.69  fof(f47,plain,(
% 0.60/0.69    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.60/0.69    inference(definition_folding,[],[f37,f46,f45,f44])).
% 0.60/0.69  fof(f45,plain,(
% 0.60/0.69    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.60/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.60/0.69  fof(f46,plain,(
% 0.60/0.69    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.60/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.60/0.69  fof(f37,plain,(
% 0.60/0.69    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.60/0.69    inference(flattening,[],[f36])).
% 0.60/0.69  fof(f36,plain,(
% 0.60/0.69    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.60/0.69    inference(ennf_transformation,[],[f15])).
% 0.60/0.69  fof(f15,axiom,(
% 0.60/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.60/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.60/0.69  fof(f189,plain,(
% 0.60/0.69    sK4 = k1_relat_1(sK7) | sP1(sK4,sK5) | ~sP2(sK4,sK7,sK5)),
% 0.60/0.69    inference(subsumption_resolution,[],[f185,f60])).
% 0.60/0.69  fof(f60,plain,(
% 0.60/0.69    v1_funct_2(sK7,sK4,sK5)),
% 0.60/0.69    inference(cnf_transformation,[],[f49])).
% 0.60/0.69  fof(f185,plain,(
% 0.60/0.69    sK4 = k1_relat_1(sK7) | ~v1_funct_2(sK7,sK4,sK5) | sP1(sK4,sK5) | ~sP2(sK4,sK7,sK5)),
% 0.60/0.69    inference(superposition,[],[f111,f87])).
% 0.60/0.69  fof(f87,plain,(
% 0.60/0.69    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.60/0.69    inference(cnf_transformation,[],[f57])).
% 0.60/0.69  fof(f57,plain,(
% 0.60/0.69    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.60/0.69    inference(rectify,[],[f56])).
% 0.60/0.69  fof(f56,plain,(
% 0.60/0.69    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.60/0.69    inference(nnf_transformation,[],[f45])).
% 0.60/0.69  fof(f111,plain,(
% 0.60/0.69    k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7)),
% 0.60/0.69    inference(resolution,[],[f61,f83])).
% 0.60/0.70  fof(f83,plain,(
% 0.60/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.60/0.70    inference(cnf_transformation,[],[f34])).
% 0.60/0.70  fof(f34,plain,(
% 0.60/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.60/0.70    inference(ennf_transformation,[],[f14])).
% 0.60/0.70  fof(f14,axiom,(
% 0.60/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.60/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.60/0.70  fof(f350,plain,(
% 0.60/0.70    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK7)) | v1_funct_2(k7_relat_1(sK7,X0),X0,sK5)) )),
% 0.60/0.70    inference(subsumption_resolution,[],[f349,f110])).
% 0.60/0.70  fof(f349,plain,(
% 0.60/0.70    ( ! [X0] : (v1_funct_2(k7_relat_1(sK7,X0),X0,sK5) | ~r1_tarski(X0,k1_relat_1(sK7)) | ~v1_relat_1(sK7)) )),
% 0.60/0.70    inference(superposition,[],[f298,f72])).
% 0.60/0.70  fof(f1297,plain,(
% 0.60/0.70    m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 0.60/0.70    inference(superposition,[],[f299,f1003])).
% 0.60/0.70  fof(f1003,plain,(
% 0.60/0.70    sK6 = k1_relat_1(k7_relat_1(sK7,sK6))),
% 0.60/0.70    inference(resolution,[],[f944,f62])).
% 0.60/0.70  fof(f944,plain,(
% 0.60/0.70    ( ! [X3] : (~r1_tarski(X3,sK4) | k1_relat_1(k7_relat_1(sK7,X3)) = X3) )),
% 0.60/0.70    inference(backward_demodulation,[],[f124,f924])).
% 0.60/0.70  fof(f924,plain,(
% 0.60/0.70    sK4 = k1_relat_1(sK7)),
% 0.60/0.70    inference(forward_demodulation,[],[f923,f640])).
% 0.60/0.70  fof(f640,plain,(
% 0.60/0.70    sK4 = k1_relset_1(sK4,k2_relat_1(sK7),sK7)),
% 0.60/0.70    inference(subsumption_resolution,[],[f505,f613])).
% 0.60/0.70  fof(f505,plain,(
% 0.60/0.70    sK4 = k1_relset_1(sK4,k2_relat_1(sK7),sK7) | k1_xboole_0 = sK5),
% 0.60/0.70    inference(superposition,[],[f466,f218])).
% 0.60/0.70  fof(f466,plain,(
% 0.60/0.70    k1_relat_1(sK7) = k1_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)),
% 0.60/0.70    inference(resolution,[],[f459,f83])).
% 0.60/0.70  fof(f459,plain,(
% 0.60/0.70    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))),
% 0.60/0.70    inference(resolution,[],[f204,f97])).
% 0.60/0.70  fof(f97,plain,(
% 0.60/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.60/0.70    inference(equality_resolution,[],[f79])).
% 0.60/0.70  fof(f79,plain,(
% 0.60/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.60/0.70    inference(cnf_transformation,[],[f53])).
% 0.60/0.70  fof(f204,plain,(
% 0.60/0.70    ( ! [X2] : (~r1_tarski(k2_relat_1(sK7),X2) | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X2)))) )),
% 0.60/0.70    inference(resolution,[],[f201,f77])).
% 0.60/0.70  fof(f77,plain,(
% 0.60/0.70    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 0.60/0.70    inference(cnf_transformation,[],[f51])).
% 0.60/0.70  fof(f201,plain,(
% 0.60/0.70    ( ! [X9] : (sP0(X9,sK7) | ~r1_tarski(k2_relat_1(sK7),X9)) )),
% 0.60/0.70    inference(subsumption_resolution,[],[f105,f110])).
% 0.60/0.70  fof(f105,plain,(
% 0.60/0.70    ( ! [X9] : (sP0(X9,sK7) | ~r1_tarski(k2_relat_1(sK7),X9) | ~v1_relat_1(sK7)) )),
% 0.60/0.70    inference(resolution,[],[f59,f78])).
% 0.60/0.70  fof(f923,plain,(
% 0.60/0.70    k1_relat_1(sK7) = k1_relset_1(sK4,k2_relat_1(sK7),sK7)),
% 0.60/0.70    inference(subsumption_resolution,[],[f563,f613])).
% 0.60/0.70  fof(f563,plain,(
% 0.60/0.70    k1_xboole_0 = sK5 | k1_relat_1(sK7) = k1_relset_1(sK4,k2_relat_1(sK7),sK7)),
% 0.60/0.70    inference(resolution,[],[f473,f83])).
% 0.60/0.70  fof(f473,plain,(
% 0.60/0.70    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(sK7)))) | k1_xboole_0 = sK5),
% 0.60/0.70    inference(superposition,[],[f459,f218])).
% 0.60/0.70  % (3260)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.60/0.70  fof(f299,plain,(
% 0.60/0.70    ( ! [X2] : (m1_subset_1(k7_relat_1(sK7,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK7,X2)),sK5)))) )),
% 0.60/0.70    inference(resolution,[],[f296,f77])).
% 0.60/0.70  % SZS output end Proof for theBenchmark
% 0.60/0.70  % (3253)------------------------------
% 0.60/0.70  % (3253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.60/0.70  % (3253)Termination reason: Refutation
% 0.60/0.70  
% 0.60/0.70  % (3253)Memory used [KB]: 2046
% 0.60/0.70  % (3253)Time elapsed: 0.119 s
% 0.60/0.70  % (3253)------------------------------
% 0.60/0.70  % (3253)------------------------------
% 0.60/0.70  % (3261)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.60/0.70  % (3110)Success in time 0.333 s
%------------------------------------------------------------------------------

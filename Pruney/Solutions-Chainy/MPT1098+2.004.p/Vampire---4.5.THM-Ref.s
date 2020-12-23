%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 210 expanded)
%              Number of leaves         :   16 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  248 ( 731 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f135,f1452])).

fof(f1452,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1451])).

fof(f1451,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1450,f547])).

fof(f547,plain,(
    v1_finset_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f536,f326])).

fof(f326,plain,(
    ! [X1] : v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),X1))) ),
    inference(resolution,[],[f59,f107])).

fof(f107,plain,(
    v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f106,f32])).

fof(f32,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
        | ~ r1_tarski(X3,sK1)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
          | ~ r1_tarski(X3,sK1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(f106,plain,
    ( v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_finset_1(sK3(X0,X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ v1_finset_1(X1)
      | v1_finset_1(k1_relat_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(f536,plain,
    ( ~ v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f315,f41])).

fof(f315,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f314,f136])).

fof(f136,plain,(
    v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f131,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f131,plain,
    ( v1_relat_1(sK0)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f314,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f302,f38])).

fof(f302,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f130,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f130,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f129,f32])).

fof(f129,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f53,f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1450,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1438,f336])).

fof(f336,plain,
    ( r1_tarski(k1_relat_1(sK0),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f80,f96])).

fof(f96,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_4
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(k2_zfmisc_1(X3,X4)))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1438,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),sK1)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f1400,f34])).

fof(f34,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1400,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),sK2)) ),
    inference(resolution,[],[f901,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f901,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),sK2))) ),
    inference(resolution,[],[f374,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f374,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(subsumption_resolution,[],[f367,f136])).

fof(f367,plain,(
    ! [X0] :
      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f341,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f341,plain,(
    r1_tarski(k2_relat_1(sK0),sK2) ),
    inference(resolution,[],[f81,f138])).

fof(f138,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f137,f136])).

fof(f137,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f101,f38])).

fof(f101,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,k2_relat_1(k2_zfmisc_1(X7,X6)))
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f135,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f133,f38])).

fof(f133,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f131,f92])).

fof(f92,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f97,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f88,f94,f90])).

fof(f88,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f86,f38])).

fof(f86,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f35,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (22065)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.46  % (22074)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (22077)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (22069)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (22057)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (22068)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (22055)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (22061)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (22060)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (22073)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (22059)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (22058)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (22075)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (22076)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (22067)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (22071)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (22063)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (22079)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (22056)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (22064)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (22072)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (22062)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (22080)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (22065)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (22078)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1462,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f97,f135,f1452])).
% 0.20/0.53  fof(f1452,plain,(
% 0.20/0.53    ~spl5_4),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1451])).
% 0.20/0.53  fof(f1451,plain,(
% 0.20/0.53    $false | ~spl5_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f1450,f547])).
% 0.20/0.53  fof(f547,plain,(
% 0.20/0.53    v1_finset_1(k1_relat_1(sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f536,f326])).
% 0.20/0.53  fof(f326,plain,(
% 0.20/0.53    ( ! [X1] : (v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),X1)))) )),
% 0.20/0.53    inference(resolution,[],[f59,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f106,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    v1_finset_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    v1_finset_1(sK3(sK0,sK1,sK2)) | ~v1_finset_1(sK0)),
% 0.20/0.53    inference(resolution,[],[f49,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_finset_1(sK3(X0,X1,X2)) | ~v1_finset_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~v1_finset_1(X1) | v1_finset_1(k1_relat_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f41,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).
% 0.20/0.53  fof(f536,plain,(
% 0.20/0.53    ~v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) | v1_finset_1(k1_relat_1(sK0))),
% 0.20/0.53    inference(resolution,[],[f315,f41])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))),
% 0.20/0.53    inference(subsumption_resolution,[],[f314,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f131,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    v1_relat_1(sK0) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.53    inference(resolution,[],[f65,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.53    inference(resolution,[],[f46,f33])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) | ~v1_relat_1(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f302,f38])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) | ~v1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | ~v1_relat_1(sK0)),
% 0.20/0.53    inference(resolution,[],[f130,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f129,f32])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | ~v1_finset_1(sK0)),
% 0.20/0.54    inference(resolution,[],[f53,f33])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) | ~v1_finset_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f1450,plain,(
% 0.20/0.54    ~v1_finset_1(k1_relat_1(sK0)) | ~spl5_4),
% 0.20/0.54    inference(subsumption_resolution,[],[f1438,f336])).
% 0.20/0.54  fof(f336,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(sK0),sK1) | ~spl5_4),
% 0.20/0.54    inference(resolution,[],[f80,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl5_4 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X4,X2,X3] : (~r1_tarski(X2,k1_relat_1(k2_zfmisc_1(X3,X4))) | r1_tarski(X2,X3)) )),
% 0.20/0.54    inference(resolution,[],[f48,f40])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.54  fof(f1438,plain,(
% 0.20/0.54    ~r1_tarski(k1_relat_1(sK0),sK1) | ~v1_finset_1(k1_relat_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f1400,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f1400,plain,(
% 0.20/0.54    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),sK2))),
% 0.20/0.54    inference(resolution,[],[f901,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f901,plain,(
% 0.20/0.54    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),sK2)))),
% 0.20/0.54    inference(resolution,[],[f374,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f367,f136])).
% 0.20/0.54  fof(f367,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) )),
% 0.20/0.54    inference(resolution,[],[f341,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.54  fof(f341,plain,(
% 0.20/0.54    r1_tarski(k2_relat_1(sK0),sK2)),
% 0.20/0.54    inference(resolution,[],[f81,f138])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f137,f136])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f101,f38])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | ~v1_relat_1(sK0)),
% 0.20/0.54    inference(resolution,[],[f36,f33])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X6,X7,X5] : (~r1_tarski(X5,k2_relat_1(k2_zfmisc_1(X7,X6))) | r1_tarski(X5,X6)) )),
% 0.20/0.54    inference(resolution,[],[f48,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    spl5_3),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    $false | spl5_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f133,f38])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl5_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f131,f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ~v1_relat_1(sK0) | spl5_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    spl5_3 <=> v1_relat_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ~spl5_3 | spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f88,f94,f90])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f86,f38])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | ~v1_relat_1(sK0)),
% 0.20/0.54    inference(resolution,[],[f35,f33])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (22065)------------------------------
% 0.20/0.54  % (22065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22065)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (22065)Memory used [KB]: 11897
% 0.20/0.54  % (22065)Time elapsed: 0.126 s
% 0.20/0.54  % (22065)------------------------------
% 0.20/0.54  % (22065)------------------------------
% 0.20/0.54  % (22054)Success in time 0.185 s
%------------------------------------------------------------------------------

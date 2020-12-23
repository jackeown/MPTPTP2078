%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:20 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 691 expanded)
%              Number of leaves         :   20 ( 170 expanded)
%              Depth                    :   21
%              Number of atoms          :  525 (3846 expanded)
%              Number of equality atoms :  106 ( 646 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f620,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f97,f138,f434,f452,f505,f597])).

fof(f597,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f595,f123])).

fof(f123,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f121,f49])).

fof(f49,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f121,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f120,f52])).

fof(f52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f120,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f118,f53])).

fof(f53,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f63,f48])).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f595,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f594,f550])).

fof(f550,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f549,f52])).

fof(f549,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f548,f53])).

fof(f548,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f547,f472])).

fof(f472,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f45,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f547,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f363,f50])).

fof(f363,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f199,f48])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f198,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f198,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = k2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f196,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f196,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = k2_funct_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f148,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f148,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f147,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f147,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_relat_1(X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f146,f63])).

fof(f146,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k1_relat_1(X1),k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f594,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f593,f134])).

fof(f593,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f84,f467])).

fof(f467,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f505,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f503,f50])).

fof(f503,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f489,f48])).

fof(f489,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | spl3_3
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f449,f134])).

fof(f449,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f448,f94])).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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

fof(f448,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f447,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f447,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f446,f45])).

fof(f446,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(superposition,[],[f435,f60])).

fof(f435,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl3_3 ),
    inference(resolution,[],[f87,f290])).

fof(f290,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) ) ),
    inference(subsumption_resolution,[],[f289,f94])).

fof(f289,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f288,f42])).

fof(f288,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f282,f45])).

fof(f282,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f144,f128])).

fof(f128,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f126,f44])).

fof(f126,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f66,f46])).

fof(f46,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f144,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f143,f57])).

fof(f143,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f142,f58])).

fof(f142,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f64,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f452,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f450,f182])).

fof(f182,plain,
    ( r1_tarski(sK0,sK0)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f177,f94])).

fof(f177,plain,
    ( r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(superposition,[],[f100,f166])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f162,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_5 ),
    inference(superposition,[],[f158,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f158,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f157,f137])).

fof(f137,plain,
    ( k1_xboole_0 != sK1
    | spl3_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f154,f43])).

fof(f43,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f154,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f68,f44])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f61,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f450,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_3
    | spl3_5 ),
    inference(forward_demodulation,[],[f449,f166])).

fof(f434,plain,
    ( spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f432,f182])).

fof(f432,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_2
    | spl3_5 ),
    inference(resolution,[],[f318,f84])).

fof(f318,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(sK0,X0) )
    | spl3_5 ),
    inference(forward_demodulation,[],[f317,f166])).

fof(f317,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(subsumption_resolution,[],[f316,f94])).

fof(f316,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f315,f42])).

fof(f315,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f314,f45])).

fof(f314,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f268,f60])).

fof(f268,plain,(
    ! [X3] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | v1_funct_2(k2_funct_1(sK2),sK1,X3) ) ),
    inference(subsumption_resolution,[],[f267,f94])).

fof(f267,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X3)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f266,f42])).

fof(f266,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X3)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f263,f45])).

fof(f263,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X3)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f125,f128])).

fof(f125,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f119,f58])).

fof(f119,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f63,f59])).

fof(f138,plain,
    ( spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f131,f136,f133])).

fof(f131,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f129,f94])).

fof(f129,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f56,f128])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f94,f91])).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f58,f81])).

fof(f81,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f47,f86,f83,f80])).

fof(f47,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n011.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:26:57 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.41  % (21344)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.41  % (21339)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.17/0.41  % (21334)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.17/0.42  % (21334)Refutation found. Thanks to Tanya!
% 0.17/0.42  % SZS status Theorem for theBenchmark
% 0.17/0.42  % (21335)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.17/0.42  % (21343)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.17/0.42  % (21336)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.17/0.42  % (21351)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.17/0.43  % (21333)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.44  % (21333)Refutation not found, incomplete strategy% (21333)------------------------------
% 0.17/0.44  % (21333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.44  % (21333)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.44  
% 0.17/0.44  % (21333)Memory used [KB]: 10618
% 0.17/0.44  % (21333)Time elapsed: 0.052 s
% 0.17/0.44  % (21333)------------------------------
% 0.17/0.44  % (21333)------------------------------
% 0.17/0.44  % (21347)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.17/0.44  % (21350)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.17/0.44  % (21352)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.17/0.44  % (21349)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.17/0.44  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f620,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(avatar_sat_refutation,[],[f88,f97,f138,f434,f452,f505,f597])).
% 0.17/0.45  fof(f597,plain,(
% 0.17/0.45    spl3_2 | ~spl3_4 | ~spl3_5),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f596])).
% 0.17/0.45  fof(f596,plain,(
% 0.17/0.45    $false | (spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.17/0.45    inference(subsumption_resolution,[],[f595,f123])).
% 0.17/0.45  fof(f123,plain,(
% 0.17/0.45    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f122,f50])).
% 0.17/0.45  fof(f50,plain,(
% 0.17/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f1])).
% 0.17/0.45  fof(f1,axiom,(
% 0.17/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.17/0.45  fof(f122,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.17/0.45    inference(forward_demodulation,[],[f121,f49])).
% 0.17/0.45  fof(f49,plain,(
% 0.17/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(cnf_transformation,[],[f6])).
% 0.17/0.45  fof(f6,axiom,(
% 0.17/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.17/0.45  fof(f121,plain,(
% 0.17/0.45    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f120,f52])).
% 0.17/0.45  fof(f52,plain,(
% 0.17/0.45    v1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(cnf_transformation,[],[f40])).
% 0.17/0.45  fof(f40,plain,(
% 0.17/0.45    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(rectify,[],[f19])).
% 0.17/0.45  fof(f19,plain,(
% 0.17/0.45    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 0.17/0.45    inference(pure_predicate_removal,[],[f18])).
% 0.17/0.45  fof(f18,plain,(
% 0.17/0.45    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.17/0.45    inference(pure_predicate_removal,[],[f10])).
% 0.17/0.45  fof(f10,axiom,(
% 0.17/0.45    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.17/0.45  fof(f120,plain,(
% 0.17/0.45    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f118,f53])).
% 0.17/0.45  fof(f53,plain,(
% 0.17/0.45    v1_funct_1(k1_xboole_0)),
% 0.17/0.45    inference(cnf_transformation,[],[f40])).
% 0.17/0.45  fof(f118,plain,(
% 0.17/0.45    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.17/0.45    inference(superposition,[],[f63,f48])).
% 0.17/0.45  fof(f48,plain,(
% 0.17/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(cnf_transformation,[],[f6])).
% 0.17/0.45  fof(f63,plain,(
% 0.17/0.45    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f32])).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(flattening,[],[f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.17/0.45    inference(ennf_transformation,[],[f15])).
% 0.17/0.45  fof(f15,axiom,(
% 0.17/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.17/0.45  fof(f595,plain,(
% 0.17/0.45    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.17/0.45    inference(forward_demodulation,[],[f594,f550])).
% 0.17/0.45  fof(f550,plain,(
% 0.17/0.45    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_4),
% 0.17/0.45    inference(subsumption_resolution,[],[f549,f52])).
% 0.17/0.45  fof(f549,plain,(
% 0.17/0.45    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.17/0.45    inference(subsumption_resolution,[],[f548,f53])).
% 0.17/0.45  fof(f548,plain,(
% 0.17/0.45    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.17/0.45    inference(subsumption_resolution,[],[f547,f472])).
% 0.17/0.45  fof(f472,plain,(
% 0.17/0.45    v2_funct_1(k1_xboole_0) | ~spl3_4),
% 0.17/0.45    inference(backward_demodulation,[],[f45,f134])).
% 0.17/0.45  fof(f134,plain,(
% 0.17/0.45    k1_xboole_0 = sK2 | ~spl3_4),
% 0.17/0.45    inference(avatar_component_clause,[],[f133])).
% 0.17/0.45  fof(f133,plain,(
% 0.17/0.45    spl3_4 <=> k1_xboole_0 = sK2),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.17/0.45  fof(f45,plain,(
% 0.17/0.45    v2_funct_1(sK2)),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  fof(f39,plain,(
% 0.17/0.45    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f38])).
% 0.17/0.45  fof(f38,plain,(
% 0.17/0.45    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f22,plain,(
% 0.17/0.45    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.17/0.45    inference(flattening,[],[f21])).
% 0.17/0.45  fof(f21,plain,(
% 0.17/0.45    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.17/0.45    inference(ennf_transformation,[],[f17])).
% 0.17/0.45  fof(f17,negated_conjecture,(
% 0.17/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.17/0.45    inference(negated_conjecture,[],[f16])).
% 0.17/0.45  fof(f16,conjecture,(
% 0.17/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.17/0.45  fof(f547,plain,(
% 0.17/0.45    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(subsumption_resolution,[],[f363,f50])).
% 0.17/0.45  fof(f363,plain,(
% 0.17/0.45    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(superposition,[],[f199,f48])).
% 0.17/0.45  fof(f199,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f198,f57])).
% 0.17/0.45  fof(f57,plain,(
% 0.17/0.45    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f27])).
% 0.17/0.45  fof(f27,plain,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(flattening,[],[f26])).
% 0.17/0.45  fof(f26,plain,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f8])).
% 0.17/0.45  fof(f8,axiom,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.17/0.45  fof(f198,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = k2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f196,f58])).
% 0.17/0.45  fof(f58,plain,(
% 0.17/0.45    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f27])).
% 0.17/0.45  fof(f196,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = k2_funct_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(superposition,[],[f148,f60])).
% 0.17/0.45  fof(f60,plain,(
% 0.17/0.45    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f29])).
% 0.17/0.45  fof(f29,plain,(
% 0.17/0.45    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(flattening,[],[f28])).
% 0.17/0.45  fof(f28,plain,(
% 0.17/0.45    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f9])).
% 0.17/0.45  fof(f9,axiom,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.17/0.45  fof(f148,plain,(
% 0.17/0.45    ( ! [X1] : (~r1_tarski(k2_relat_1(X1),k1_xboole_0) | k1_xboole_0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f147,f55])).
% 0.17/0.45  fof(f55,plain,(
% 0.17/0.45    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f25])).
% 0.17/0.45  fof(f25,plain,(
% 0.17/0.45    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(flattening,[],[f24])).
% 0.17/0.45  fof(f24,plain,(
% 0.17/0.45    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f7])).
% 0.17/0.45  fof(f7,axiom,(
% 0.17/0.45    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.17/0.45  fof(f147,plain,(
% 0.17/0.45    ( ! [X1] : (k1_xboole_0 = k1_relat_1(X1) | k1_xboole_0 = X1 | ~r1_tarski(k2_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f146,f63])).
% 0.17/0.45  fof(f146,plain,(
% 0.17/0.45    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(X1),k1_xboole_0) | k1_xboole_0 = k1_relat_1(X1) | k1_xboole_0 = X1 | ~r1_tarski(k2_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(resolution,[],[f76,f64])).
% 0.17/0.45  fof(f64,plain,(
% 0.17/0.45    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f32])).
% 0.17/0.45  fof(f76,plain,(
% 0.17/0.45    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.17/0.45    inference(equality_resolution,[],[f72])).
% 0.17/0.45  fof(f72,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f41])).
% 0.17/0.45  fof(f41,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(nnf_transformation,[],[f37])).
% 0.17/0.45  fof(f37,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(flattening,[],[f36])).
% 0.17/0.45  fof(f36,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f14])).
% 0.17/0.45  fof(f14,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.17/0.45  fof(f594,plain,(
% 0.17/0.45    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.17/0.45    inference(forward_demodulation,[],[f593,f134])).
% 0.17/0.45  fof(f593,plain,(
% 0.17/0.45    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_5)),
% 0.17/0.45    inference(forward_demodulation,[],[f84,f467])).
% 0.17/0.45  fof(f467,plain,(
% 0.17/0.45    k1_xboole_0 = sK1 | ~spl3_5),
% 0.17/0.45    inference(avatar_component_clause,[],[f136])).
% 0.17/0.45  fof(f136,plain,(
% 0.17/0.45    spl3_5 <=> k1_xboole_0 = sK1),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.17/0.45  fof(f84,plain,(
% 0.17/0.45    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.17/0.45    inference(avatar_component_clause,[],[f83])).
% 0.17/0.45  fof(f83,plain,(
% 0.17/0.45    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.45  fof(f505,plain,(
% 0.17/0.45    spl3_3 | ~spl3_4),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f504])).
% 0.17/0.45  fof(f504,plain,(
% 0.17/0.45    $false | (spl3_3 | ~spl3_4)),
% 0.17/0.45    inference(subsumption_resolution,[],[f503,f50])).
% 0.17/0.45  fof(f503,plain,(
% 0.17/0.45    ~r1_tarski(k1_xboole_0,sK0) | (spl3_3 | ~spl3_4)),
% 0.17/0.45    inference(forward_demodulation,[],[f489,f48])).
% 0.17/0.45  fof(f489,plain,(
% 0.17/0.45    ~r1_tarski(k1_relat_1(k1_xboole_0),sK0) | (spl3_3 | ~spl3_4)),
% 0.17/0.45    inference(backward_demodulation,[],[f449,f134])).
% 0.17/0.45  fof(f449,plain,(
% 0.17/0.45    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_3),
% 0.17/0.45    inference(subsumption_resolution,[],[f448,f94])).
% 0.17/0.45  fof(f94,plain,(
% 0.17/0.45    v1_relat_1(sK2)),
% 0.17/0.45    inference(resolution,[],[f65,f44])).
% 0.17/0.45  fof(f44,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  fof(f65,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f33])).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f11])).
% 0.17/0.45  fof(f11,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.17/0.45  fof(f448,plain,(
% 0.17/0.45    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | spl3_3),
% 0.17/0.45    inference(subsumption_resolution,[],[f447,f42])).
% 0.17/0.45  fof(f42,plain,(
% 0.17/0.45    v1_funct_1(sK2)),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  fof(f447,plain,(
% 0.17/0.45    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_3),
% 0.17/0.45    inference(subsumption_resolution,[],[f446,f45])).
% 0.17/0.45  fof(f446,plain,(
% 0.17/0.45    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_3),
% 0.17/0.45    inference(superposition,[],[f435,f60])).
% 0.17/0.45  fof(f435,plain,(
% 0.17/0.45    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl3_3),
% 0.17/0.45    inference(resolution,[],[f87,f290])).
% 0.17/0.45  fof(f290,plain,(
% 0.17/0.45    ( ! [X3] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f289,f94])).
% 0.17/0.45  fof(f289,plain,(
% 0.17/0.45    ( ! [X3] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f288,f42])).
% 0.17/0.45  fof(f288,plain,(
% 0.17/0.45    ( ! [X3] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f282,f45])).
% 0.17/0.45  fof(f282,plain,(
% 0.17/0.45    ( ! [X3] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(superposition,[],[f144,f128])).
% 0.17/0.45  fof(f128,plain,(
% 0.17/0.45    sK1 = k2_relat_1(sK2)),
% 0.17/0.45    inference(subsumption_resolution,[],[f126,f44])).
% 0.17/0.45  fof(f126,plain,(
% 0.17/0.45    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.17/0.45    inference(superposition,[],[f66,f46])).
% 0.17/0.45  fof(f46,plain,(
% 0.17/0.45    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  fof(f66,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f34])).
% 0.17/0.45  fof(f34,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f13])).
% 0.17/0.45  fof(f13,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.17/0.45  fof(f144,plain,(
% 0.17/0.45    ( ! [X2,X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f143,f57])).
% 0.17/0.45  fof(f143,plain,(
% 0.17/0.45    ( ! [X2,X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f142,f58])).
% 0.17/0.45  fof(f142,plain,(
% 0.17/0.45    ( ! [X2,X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(superposition,[],[f64,f59])).
% 0.17/0.45  fof(f59,plain,(
% 0.17/0.45    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f29])).
% 0.17/0.45  fof(f87,plain,(
% 0.17/0.45    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.17/0.45    inference(avatar_component_clause,[],[f86])).
% 0.17/0.45  fof(f86,plain,(
% 0.17/0.45    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.45  fof(f452,plain,(
% 0.17/0.45    spl3_3 | spl3_5),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f451])).
% 0.17/0.45  fof(f451,plain,(
% 0.17/0.45    $false | (spl3_3 | spl3_5)),
% 0.17/0.45    inference(subsumption_resolution,[],[f450,f182])).
% 0.17/0.45  fof(f182,plain,(
% 0.17/0.45    r1_tarski(sK0,sK0) | spl3_5),
% 0.17/0.45    inference(subsumption_resolution,[],[f177,f94])).
% 0.17/0.45  fof(f177,plain,(
% 0.17/0.45    r1_tarski(sK0,sK0) | ~v1_relat_1(sK2) | spl3_5),
% 0.17/0.45    inference(superposition,[],[f100,f166])).
% 0.17/0.45  fof(f166,plain,(
% 0.17/0.45    sK0 = k1_relat_1(sK2) | spl3_5),
% 0.17/0.45    inference(subsumption_resolution,[],[f162,f44])).
% 0.17/0.45  fof(f162,plain,(
% 0.17/0.45    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_5),
% 0.17/0.45    inference(superposition,[],[f158,f67])).
% 0.17/0.45  fof(f67,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f35])).
% 0.17/0.45  fof(f35,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f12])).
% 0.17/0.45  fof(f12,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.17/0.45  fof(f158,plain,(
% 0.17/0.45    sK0 = k1_relset_1(sK0,sK1,sK2) | spl3_5),
% 0.17/0.45    inference(subsumption_resolution,[],[f157,f137])).
% 0.17/0.45  fof(f137,plain,(
% 0.17/0.45    k1_xboole_0 != sK1 | spl3_5),
% 0.17/0.45    inference(avatar_component_clause,[],[f136])).
% 0.17/0.45  fof(f157,plain,(
% 0.17/0.45    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.17/0.45    inference(subsumption_resolution,[],[f154,f43])).
% 0.17/0.45  fof(f43,plain,(
% 0.17/0.45    v1_funct_2(sK2,sK0,sK1)),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  fof(f154,plain,(
% 0.17/0.45    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.17/0.45    inference(resolution,[],[f68,f44])).
% 0.17/0.45  fof(f68,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.17/0.45    inference(cnf_transformation,[],[f41])).
% 0.17/0.45  fof(f100,plain,(
% 0.17/0.45    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(duplicate_literal_removal,[],[f99])).
% 0.17/0.45  fof(f99,plain,(
% 0.17/0.45    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(superposition,[],[f61,f54])).
% 0.17/0.45  fof(f54,plain,(
% 0.17/0.45    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f23])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f5])).
% 0.17/0.45  fof(f5,axiom,(
% 0.17/0.45    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.17/0.45  fof(f61,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f30])).
% 0.17/0.45  fof(f30,plain,(
% 0.17/0.45    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f4])).
% 0.17/0.45  fof(f4,axiom,(
% 0.17/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.17/0.45  fof(f450,plain,(
% 0.17/0.45    ~r1_tarski(sK0,sK0) | (spl3_3 | spl3_5)),
% 0.17/0.45    inference(forward_demodulation,[],[f449,f166])).
% 0.17/0.45  fof(f434,plain,(
% 0.17/0.45    spl3_2 | spl3_5),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f433])).
% 0.17/0.45  fof(f433,plain,(
% 0.17/0.45    $false | (spl3_2 | spl3_5)),
% 0.17/0.45    inference(subsumption_resolution,[],[f432,f182])).
% 0.17/0.45  fof(f432,plain,(
% 0.17/0.45    ~r1_tarski(sK0,sK0) | (spl3_2 | spl3_5)),
% 0.17/0.45    inference(resolution,[],[f318,f84])).
% 0.17/0.45  fof(f318,plain,(
% 0.17/0.45    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(sK0,X0)) ) | spl3_5),
% 0.17/0.45    inference(forward_demodulation,[],[f317,f166])).
% 0.17/0.45  fof(f317,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f316,f94])).
% 0.17/0.45  fof(f316,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f315,f42])).
% 0.17/0.45  fof(f315,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f314,f45])).
% 0.17/0.45  fof(f314,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(superposition,[],[f268,f60])).
% 0.17/0.45  fof(f268,plain,(
% 0.17/0.45    ( ! [X3] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | v1_funct_2(k2_funct_1(sK2),sK1,X3)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f267,f94])).
% 0.17/0.45  fof(f267,plain,(
% 0.17/0.45    ( ! [X3] : (v1_funct_2(k2_funct_1(sK2),sK1,X3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f266,f42])).
% 0.17/0.45  fof(f266,plain,(
% 0.17/0.45    ( ! [X3] : (v1_funct_2(k2_funct_1(sK2),sK1,X3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f263,f45])).
% 0.17/0.45  fof(f263,plain,(
% 0.17/0.45    ( ! [X3] : (v1_funct_2(k2_funct_1(sK2),sK1,X3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.17/0.45    inference(superposition,[],[f125,f128])).
% 0.17/0.45  fof(f125,plain,(
% 0.17/0.45    ( ! [X2,X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f124,f57])).
% 0.17/0.45  fof(f124,plain,(
% 0.17/0.45    ( ! [X2,X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f119,f58])).
% 0.17/0.45  fof(f119,plain,(
% 0.17/0.45    ( ! [X2,X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(superposition,[],[f63,f59])).
% 0.17/0.45  fof(f138,plain,(
% 0.17/0.45    spl3_4 | ~spl3_5),
% 0.17/0.45    inference(avatar_split_clause,[],[f131,f136,f133])).
% 0.17/0.45  fof(f131,plain,(
% 0.17/0.45    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 0.17/0.45    inference(subsumption_resolution,[],[f129,f94])).
% 0.17/0.45  fof(f129,plain,(
% 0.17/0.45    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 0.17/0.45    inference(superposition,[],[f56,f128])).
% 0.17/0.45  fof(f56,plain,(
% 0.17/0.45    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f25])).
% 0.17/0.45  fof(f97,plain,(
% 0.17/0.45    spl3_1),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f96])).
% 0.17/0.45  fof(f96,plain,(
% 0.17/0.45    $false | spl3_1),
% 0.17/0.45    inference(subsumption_resolution,[],[f94,f91])).
% 0.17/0.45  fof(f91,plain,(
% 0.17/0.45    ~v1_relat_1(sK2) | spl3_1),
% 0.17/0.45    inference(subsumption_resolution,[],[f90,f42])).
% 0.17/0.45  fof(f90,plain,(
% 0.17/0.45    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.17/0.45    inference(resolution,[],[f58,f81])).
% 0.17/0.45  fof(f81,plain,(
% 0.17/0.45    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.17/0.45    inference(avatar_component_clause,[],[f80])).
% 0.17/0.45  fof(f80,plain,(
% 0.17/0.45    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.45  fof(f88,plain,(
% 0.17/0.45    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.17/0.45    inference(avatar_split_clause,[],[f47,f86,f83,f80])).
% 0.17/0.45  fof(f47,plain,(
% 0.17/0.45    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  % SZS output end Proof for theBenchmark
% 0.17/0.45  % (21334)------------------------------
% 0.17/0.45  % (21334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (21334)Termination reason: Refutation
% 0.17/0.45  
% 0.17/0.45  % (21334)Memory used [KB]: 10874
% 0.17/0.45  % (21334)Time elapsed: 0.054 s
% 0.17/0.45  % (21334)------------------------------
% 0.17/0.45  % (21334)------------------------------
% 0.17/0.45  % (21331)Success in time 0.121 s
%------------------------------------------------------------------------------

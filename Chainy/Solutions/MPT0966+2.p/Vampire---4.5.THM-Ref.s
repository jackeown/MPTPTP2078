%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0966+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 588 expanded)
%              Number of leaves         :   20 ( 154 expanded)
%              Depth                    :   18
%              Number of atoms          :  359 (3165 expanded)
%              Number of equality atoms :  113 ( 880 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5722,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3467,f3901,f3903,f4205,f4234,f5692,f5721])).

fof(f5721,plain,
    ( ~ spl163_2
    | spl163_4 ),
    inference(avatar_contradiction_clause,[],[f5720])).

fof(f5720,plain,
    ( $false
    | ~ spl163_2
    | spl163_4 ),
    inference(subsumption_resolution,[],[f5719,f4900])).

fof(f4900,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK29)
    | ~ spl163_2 ),
    inference(backward_demodulation,[],[f4434,f4538])).

fof(f4538,plain,
    ( k1_xboole_0 = sK30
    | ~ spl163_2 ),
    inference(forward_demodulation,[],[f4537,f2909])).

fof(f2909,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f4537,plain,
    ( sK30 = k3_xboole_0(sK30,k1_xboole_0)
    | ~ spl163_2 ),
    inference(forward_demodulation,[],[f4442,f3067])).

fof(f3067,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f2397])).

fof(f2397,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2021])).

fof(f2021,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2020])).

fof(f2020,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4442,plain,
    ( sK30 = k3_xboole_0(sK30,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK30)))
    | ~ spl163_2 ),
    inference(backward_demodulation,[],[f3504,f4431])).

fof(f4431,plain,
    ( k1_xboole_0 = k1_relat_1(sK30)
    | ~ spl163_2 ),
    inference(forward_demodulation,[],[f4430,f3466])).

fof(f3466,plain,
    ( k1_xboole_0 = sK27
    | ~ spl163_2 ),
    inference(avatar_component_clause,[],[f3465])).

fof(f3465,plain,
    ( spl163_2
  <=> k1_xboole_0 = sK27 ),
    introduced(avatar_definition,[new_symbols(naming,[spl163_2])])).

fof(f4430,plain,
    ( sK27 = k1_relat_1(sK30)
    | ~ spl163_2 ),
    inference(subsumption_resolution,[],[f4429,f2333])).

fof(f2333,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f4429,plain,
    ( ~ r1_tarski(k1_xboole_0,sK30)
    | sK27 = k1_relat_1(sK30)
    | ~ spl163_2 ),
    inference(forward_demodulation,[],[f4289,f3061])).

fof(f3061,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f873])).

fof(f873,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f4289,plain,
    ( ~ r1_tarski(k6_relat_1(k1_xboole_0),sK30)
    | sK27 = k1_relat_1(sK30)
    | ~ spl163_2 ),
    inference(backward_demodulation,[],[f3334,f3466])).

fof(f3334,plain,
    ( sK27 = k1_relat_1(sK30)
    | ~ r1_tarski(k6_relat_1(sK27),sK30) ),
    inference(backward_demodulation,[],[f3253,f3256])).

fof(f3256,plain,(
    k1_relat_1(sK30) = k1_relset_1(sK27,sK28,sK30) ),
    inference(resolution,[],[f2327,f2800])).

fof(f2800,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f1739,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2327,plain,(
    m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK28))) ),
    inference(cnf_transformation,[],[f1979])).

fof(f1979,plain,
    ( ( ~ m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK29)))
      | ~ v1_funct_2(sK30,sK27,sK29)
      | ~ v1_funct_1(sK30) )
    & ( k1_xboole_0 = sK27
      | k1_xboole_0 != sK28 )
    & r1_tarski(k2_relset_1(sK27,sK28,sK30),sK29)
    & m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK28)))
    & v1_funct_2(sK30,sK27,sK28)
    & v1_funct_1(sK30) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28,sK29,sK30])],[f1492,f1978])).

fof(f1978,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK29)))
        | ~ v1_funct_2(sK30,sK27,sK29)
        | ~ v1_funct_1(sK30) )
      & ( k1_xboole_0 = sK27
        | k1_xboole_0 != sK28 )
      & r1_tarski(k2_relset_1(sK27,sK28,sK30),sK29)
      & m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK28)))
      & v1_funct_2(sK30,sK27,sK28)
      & v1_funct_1(sK30) ) ),
    introduced(choice_axiom,[])).

fof(f1492,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1491])).

fof(f1491,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1483])).

fof(f1483,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1482])).

fof(f1482,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f3253,plain,
    ( sK27 = k1_relset_1(sK27,sK28,sK30)
    | ~ r1_tarski(k6_relat_1(sK27),sK30) ),
    inference(resolution,[],[f2327,f2797])).

fof(f2797,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f1737])).

fof(f1737,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f1736])).

fof(f1736,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1252])).

fof(f1252,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

fof(f3504,plain,(
    sK30 = k3_xboole_0(sK30,k2_zfmisc_1(k1_relat_1(sK30),k2_relat_1(sK30))) ),
    inference(resolution,[],[f3236,f2565])).

fof(f2565,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1618])).

fof(f1618,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f826])).

fof(f826,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f3236,plain,(
    v1_relat_1(sK30) ),
    inference(resolution,[],[f2327,f2391])).

fof(f2391,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1537])).

fof(f1537,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4434,plain,
    ( v1_funct_2(sK30,k1_xboole_0,sK29)
    | ~ spl163_2 ),
    inference(backward_demodulation,[],[f3441,f4431])).

fof(f3441,plain,(
    v1_funct_2(sK30,k1_relat_1(sK30),sK29) ),
    inference(subsumption_resolution,[],[f3440,f3236])).

fof(f3440,plain,
    ( v1_funct_2(sK30,k1_relat_1(sK30),sK29)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f3356,f2325])).

fof(f2325,plain,(
    v1_funct_1(sK30) ),
    inference(cnf_transformation,[],[f1979])).

fof(f3356,plain,
    ( v1_funct_2(sK30,k1_relat_1(sK30),sK29)
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(resolution,[],[f3319,f2432])).

fof(f2432,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f1554,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1553])).

fof(f1553,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1478])).

fof(f1478,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f3319,plain,(
    r1_tarski(k2_relat_1(sK30),sK29) ),
    inference(backward_demodulation,[],[f2328,f3229])).

fof(f3229,plain,(
    k2_relset_1(sK27,sK28,sK30) = k2_relat_1(sK30) ),
    inference(resolution,[],[f2327,f2346])).

fof(f2346,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1501])).

fof(f1501,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2328,plain,(
    r1_tarski(k2_relset_1(sK27,sK28,sK30),sK29) ),
    inference(cnf_transformation,[],[f1979])).

fof(f5719,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK29)
    | ~ spl163_2
    | spl163_4 ),
    inference(forward_demodulation,[],[f5718,f4538])).

fof(f5718,plain,
    ( ~ v1_funct_2(sK30,k1_xboole_0,sK29)
    | ~ spl163_2
    | spl163_4 ),
    inference(forward_demodulation,[],[f3897,f3466])).

fof(f3897,plain,
    ( ~ v1_funct_2(sK30,sK27,sK29)
    | spl163_4 ),
    inference(avatar_component_clause,[],[f3896])).

fof(f3896,plain,
    ( spl163_4
  <=> v1_funct_2(sK30,sK27,sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl163_4])])).

fof(f5692,plain,
    ( ~ spl163_2
    | spl163_5 ),
    inference(avatar_contradiction_clause,[],[f5691])).

fof(f5691,plain,
    ( $false
    | ~ spl163_2
    | spl163_5 ),
    inference(subsumption_resolution,[],[f5690,f4866])).

fof(f4866,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl163_2 ),
    inference(backward_demodulation,[],[f4320,f4538])).

fof(f4320,plain,
    ( m1_subset_1(sK30,k1_tarski(k1_xboole_0))
    | ~ spl163_2 ),
    inference(forward_demodulation,[],[f4319,f2684])).

fof(f2684,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f4319,plain,
    ( m1_subset_1(sK30,k1_zfmisc_1(k1_xboole_0))
    | ~ spl163_2 ),
    inference(forward_demodulation,[],[f4236,f3067])).

fof(f4236,plain,
    ( m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK28)))
    | ~ spl163_2 ),
    inference(backward_demodulation,[],[f2327,f3466])).

fof(f5690,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl163_2
    | spl163_5 ),
    inference(forward_demodulation,[],[f5689,f4538])).

fof(f5689,plain,
    ( ~ m1_subset_1(sK30,k1_tarski(k1_xboole_0))
    | ~ spl163_2
    | spl163_5 ),
    inference(forward_demodulation,[],[f5688,f2684])).

fof(f5688,plain,
    ( ~ m1_subset_1(sK30,k1_zfmisc_1(k1_xboole_0))
    | ~ spl163_2
    | spl163_5 ),
    inference(forward_demodulation,[],[f4308,f3067])).

fof(f4308,plain,
    ( ~ m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK29)))
    | ~ spl163_2
    | spl163_5 ),
    inference(backward_demodulation,[],[f3900,f3466])).

fof(f3900,plain,
    ( ~ m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK29)))
    | spl163_5 ),
    inference(avatar_component_clause,[],[f3899])).

fof(f3899,plain,
    ( spl163_5
  <=> m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK29))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl163_5])])).

fof(f4234,plain,
    ( spl163_1
    | spl163_5 ),
    inference(avatar_contradiction_clause,[],[f4233])).

fof(f4233,plain,
    ( $false
    | spl163_1
    | spl163_5 ),
    inference(subsumption_resolution,[],[f3900,f4048])).

fof(f4048,plain,
    ( m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK29)))
    | spl163_1 ),
    inference(backward_demodulation,[],[f3443,f3989])).

fof(f3989,plain,
    ( sK27 = k1_relat_1(sK30)
    | spl163_1 ),
    inference(backward_demodulation,[],[f3256,f3988])).

fof(f3988,plain,
    ( sK27 = k1_relset_1(sK27,sK28,sK30)
    | spl163_1 ),
    inference(subsumption_resolution,[],[f3987,f3463])).

fof(f3463,plain,
    ( k1_xboole_0 != sK28
    | spl163_1 ),
    inference(avatar_component_clause,[],[f3462])).

fof(f3462,plain,
    ( spl163_1
  <=> k1_xboole_0 = sK28 ),
    introduced(avatar_definition,[new_symbols(naming,[spl163_1])])).

fof(f3987,plain,
    ( sK27 = k1_relset_1(sK27,sK28,sK30)
    | k1_xboole_0 = sK28 ),
    inference(subsumption_resolution,[],[f3985,f2326])).

fof(f2326,plain,(
    v1_funct_2(sK30,sK27,sK28) ),
    inference(cnf_transformation,[],[f1979])).

fof(f3985,plain,
    ( sK27 = k1_relset_1(sK27,sK28,sK30)
    | ~ v1_funct_2(sK30,sK27,sK28)
    | k1_xboole_0 = sK28 ),
    inference(resolution,[],[f3239,f2418])).

fof(f2418,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2027])).

fof(f2027,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f2026])).

fof(f2026,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f1934])).

fof(f1934,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3239,plain,(
    sP1(sK27,sK30,sK28) ),
    inference(resolution,[],[f2327,f2422])).

fof(f2422,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2028,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1935])).

fof(f1935,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f1552,f1934])).

fof(f1552,plain,(
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
    inference(flattening,[],[f1551])).

fof(f1551,plain,(
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
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
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

fof(f3443,plain,(
    m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK30),sK29))) ),
    inference(subsumption_resolution,[],[f3442,f3236])).

fof(f3442,plain,
    ( m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK30),sK29)))
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f3357,f2325])).

fof(f3357,plain,
    ( m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK30),sK29)))
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(resolution,[],[f3319,f2433])).

fof(f2433,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f4205,plain,
    ( spl163_1
    | spl163_4 ),
    inference(avatar_contradiction_clause,[],[f4204])).

fof(f4204,plain,
    ( $false
    | spl163_1
    | spl163_4 ),
    inference(subsumption_resolution,[],[f4047,f3897])).

fof(f4047,plain,
    ( v1_funct_2(sK30,sK27,sK29)
    | spl163_1 ),
    inference(backward_demodulation,[],[f3441,f3989])).

fof(f3903,plain,(
    spl163_3 ),
    inference(avatar_contradiction_clause,[],[f3902])).

fof(f3902,plain,
    ( $false
    | spl163_3 ),
    inference(subsumption_resolution,[],[f3894,f2325])).

fof(f3894,plain,
    ( ~ v1_funct_1(sK30)
    | spl163_3 ),
    inference(avatar_component_clause,[],[f3893])).

fof(f3893,plain,
    ( spl163_3
  <=> v1_funct_1(sK30) ),
    introduced(avatar_definition,[new_symbols(naming,[spl163_3])])).

fof(f3901,plain,
    ( ~ spl163_3
    | ~ spl163_4
    | ~ spl163_5 ),
    inference(avatar_split_clause,[],[f2330,f3899,f3896,f3893])).

fof(f2330,plain,
    ( ~ m1_subset_1(sK30,k1_zfmisc_1(k2_zfmisc_1(sK27,sK29)))
    | ~ v1_funct_2(sK30,sK27,sK29)
    | ~ v1_funct_1(sK30) ),
    inference(cnf_transformation,[],[f1979])).

fof(f3467,plain,
    ( ~ spl163_1
    | spl163_2 ),
    inference(avatar_split_clause,[],[f2329,f3465,f3462])).

fof(f2329,plain,
    ( k1_xboole_0 = sK27
    | k1_xboole_0 != sK28 ),
    inference(cnf_transformation,[],[f1979])).
%------------------------------------------------------------------------------

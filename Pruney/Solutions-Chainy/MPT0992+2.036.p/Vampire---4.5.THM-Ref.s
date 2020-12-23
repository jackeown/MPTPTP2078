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
% DateTime   : Thu Dec  3 13:03:15 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  157 (1007 expanded)
%              Number of leaves         :   22 ( 244 expanded)
%              Depth                    :   24
%              Number of atoms          :  445 (6074 expanded)
%              Number of equality atoms :  121 (1371 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2063,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f117,f230,f632,f1823,f1953,f2047])).

fof(f2047,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f2046])).

fof(f2046,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | spl4_28 ),
    inference(subsumption_resolution,[],[f2022,f116])).

fof(f116,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2022,plain,
    ( k1_xboole_0 != sK0
    | ~ spl4_4
    | spl4_28 ),
    inference(forward_demodulation,[],[f2021,f1603])).

fof(f1603,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f528,f1085])).

fof(f1085,plain,(
    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    inference(resolution,[],[f527,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f527,plain,(
    r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f432,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f432,plain,(
    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f425,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f425,plain,(
    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK3,k1_xboole_0))))) ),
    inference(superposition,[],[f344,f310])).

fof(f310,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(resolution,[],[f165,f140])).

fof(f140,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41])).

fof(f41,plain,
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
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f165,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f344,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0))))) ),
    inference(subsumption_resolution,[],[f343,f233])).

fof(f233,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f184,f74])).

fof(f184,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f183,f179])).

fof(f179,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(subsumption_resolution,[],[f176,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f176,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f84,f52])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f183,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f180,f50])).

fof(f180,plain,(
    ! [X0] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f86,f52])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f343,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X0))
      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0))))) ) ),
    inference(forward_demodulation,[],[f342,f179])).

fof(f342,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0)))))
      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) ) ),
    inference(forward_demodulation,[],[f338,f179])).

fof(f338,plain,(
    ! [X0] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)),k2_relat_1(k2_partfun1(sK0,sK1,sK3,X0)))))
      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) ) ),
    inference(resolution,[],[f175,f174])).

fof(f174,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f171,f50])).

fof(f171,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f85,f52])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f175,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f65,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f528,plain,(
    ! [X2] : k1_xboole_0 = k1_relset_1(X2,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f519,f310])).

fof(f519,plain,(
    ! [X2] : k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_relset_1(X2,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) ),
    inference(resolution,[],[f432,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X1) = k1_relset_1(X0,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f75,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2021,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | spl4_28 ),
    inference(forward_demodulation,[],[f2020,f1955])).

fof(f1955,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(global_subsumption,[],[f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f2020,plain,
    ( sK0 != k1_relset_1(sK0,sK1,k1_xboole_0)
    | ~ spl4_4
    | spl4_28 ),
    inference(forward_demodulation,[],[f630,f1972])).

fof(f1972,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1971,f56])).

fof(f1971,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1970,f89])).

fof(f1970,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1969,f1955])).

fof(f1969,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1968,f89])).

fof(f1968,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1536,f1955])).

fof(f1536,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(resolution,[],[f550,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f550,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
    inference(resolution,[],[f202,f69])).

fof(f202,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(subsumption_resolution,[],[f201,f140])).

fof(f201,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f195,f50])).

fof(f195,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f194,f65])).

fof(f194,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f193,f140])).

fof(f193,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f156,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f156,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f76,f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f630,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f629])).

fof(f629,plain,
    ( spl4_28
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1953,plain,
    ( spl4_3
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f1952])).

fof(f1952,plain,
    ( $false
    | spl4_3
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1944,f246])).

fof(f246,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(superposition,[],[f107,f179])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1944,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_28 ),
    inference(superposition,[],[f413,f903])).

fof(f903,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_28 ),
    inference(resolution,[],[f739,f53])).

fof(f53,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f739,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f738,f140])).

fof(f738,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl4_28 ),
    inference(superposition,[],[f60,f734])).

fof(f734,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_28 ),
    inference(superposition,[],[f631,f168])).

fof(f168,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f75,f52])).

fof(f631,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f629])).

fof(f413,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) ),
    inference(subsumption_resolution,[],[f412,f233])).

fof(f412,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f406,f248])).

fof(f248,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[],[f174,f179])).

fof(f406,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f358,f65])).

fof(f358,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f357,f233])).

fof(f357,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f235,f61])).

fof(f235,plain,(
    ! [X2] : v5_relat_1(k7_relat_1(sK3,X2),sK1) ),
    inference(resolution,[],[f184,f76])).

fof(f1823,plain,
    ( spl4_2
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f1822])).

fof(f1822,plain,
    ( $false
    | spl4_2
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1818,f247])).

fof(f247,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(superposition,[],[f103,f179])).

fof(f103,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1818,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_28 ),
    inference(superposition,[],[f415,f903])).

fof(f415,plain,(
    ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) ),
    inference(subsumption_resolution,[],[f414,f233])).

fof(f414,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f407,f248])).

fof(f407,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
      | ~ v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f358,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f632,plain,
    ( spl4_28
    | spl4_4 ),
    inference(avatar_split_clause,[],[f188,f110,f629])).

fof(f188,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f185,f51])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f185,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f77,f52])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f230,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f174,f99])).

fof(f99,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f117,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f54,f114,f110])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f55,f105,f101,f97])).

fof(f55,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (29306)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (29326)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (29308)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (29310)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (29307)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (29319)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (29318)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (29311)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (29315)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (29305)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (29330)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (29322)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (29329)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (29328)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (29313)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (29325)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (29317)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (29309)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.28/0.53  % (29321)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.28/0.53  % (29320)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.28/0.53  % (29316)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.28/0.53  % (29323)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.28/0.54  % (29327)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.28/0.54  % (29312)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.28/0.54  % (29314)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.42/0.56  % (29324)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.42/0.58  % (29315)Refutation found. Thanks to Tanya!
% 1.42/0.58  % SZS status Theorem for theBenchmark
% 1.42/0.58  % SZS output start Proof for theBenchmark
% 1.42/0.58  fof(f2063,plain,(
% 1.42/0.58    $false),
% 1.42/0.58    inference(avatar_sat_refutation,[],[f108,f117,f230,f632,f1823,f1953,f2047])).
% 1.42/0.58  fof(f2047,plain,(
% 1.42/0.58    ~spl4_4 | ~spl4_5 | spl4_28),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f2046])).
% 1.42/0.58  fof(f2046,plain,(
% 1.42/0.58    $false | (~spl4_4 | ~spl4_5 | spl4_28)),
% 1.42/0.58    inference(subsumption_resolution,[],[f2022,f116])).
% 1.42/0.58  fof(f116,plain,(
% 1.42/0.58    k1_xboole_0 = sK0 | ~spl4_5),
% 1.42/0.58    inference(avatar_component_clause,[],[f114])).
% 1.42/0.58  fof(f114,plain,(
% 1.42/0.58    spl4_5 <=> k1_xboole_0 = sK0),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.42/0.58  fof(f2022,plain,(
% 1.42/0.58    k1_xboole_0 != sK0 | (~spl4_4 | spl4_28)),
% 1.42/0.58    inference(forward_demodulation,[],[f2021,f1603])).
% 1.42/0.58  fof(f1603,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k1_relset_1(X0,k1_xboole_0,k1_xboole_0)) )),
% 1.42/0.58    inference(superposition,[],[f528,f1085])).
% 1.42/0.58  fof(f1085,plain,(
% 1.42/0.58    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)),
% 1.42/0.58    inference(resolution,[],[f527,f57])).
% 1.42/0.58  fof(f57,plain,(
% 1.42/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f23])).
% 1.42/0.58  fof(f23,plain,(
% 1.42/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.42/0.58    inference(ennf_transformation,[],[f4])).
% 1.42/0.58  fof(f4,axiom,(
% 1.42/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.42/0.58  fof(f527,plain,(
% 1.42/0.58    r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)),
% 1.42/0.58    inference(resolution,[],[f432,f69])).
% 1.42/0.58  fof(f69,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f46])).
% 1.42/0.58  fof(f46,plain,(
% 1.42/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.42/0.58    inference(nnf_transformation,[],[f6])).
% 1.42/0.58  fof(f6,axiom,(
% 1.42/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.58  fof(f432,plain,(
% 1.42/0.58    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.42/0.58    inference(forward_demodulation,[],[f425,f90])).
% 1.42/0.58  fof(f90,plain,(
% 1.42/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.42/0.58    inference(equality_resolution,[],[f72])).
% 1.42/0.58  fof(f72,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f48])).
% 1.42/0.58  fof(f48,plain,(
% 1.42/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.42/0.58    inference(flattening,[],[f47])).
% 1.42/0.58  fof(f47,plain,(
% 1.42/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.42/0.58    inference(nnf_transformation,[],[f5])).
% 1.42/0.58  fof(f5,axiom,(
% 1.42/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.42/0.58  fof(f425,plain,(
% 1.42/0.58    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK3,k1_xboole_0)))))),
% 1.42/0.58    inference(superposition,[],[f344,f310])).
% 1.42/0.58  fof(f310,plain,(
% 1.42/0.58    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 1.42/0.58    inference(resolution,[],[f165,f140])).
% 1.42/0.58  fof(f140,plain,(
% 1.42/0.58    v1_relat_1(sK3)),
% 1.42/0.58    inference(resolution,[],[f74,f52])).
% 1.42/0.58  fof(f52,plain,(
% 1.42/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.58    inference(cnf_transformation,[],[f42])).
% 1.42/0.58  fof(f42,plain,(
% 1.42/0.58    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41])).
% 1.42/0.58  fof(f41,plain,(
% 1.42/0.58    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f22,plain,(
% 1.42/0.58    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.42/0.58    inference(flattening,[],[f21])).
% 1.42/0.58  fof(f21,plain,(
% 1.42/0.58    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.42/0.58    inference(ennf_transformation,[],[f19])).
% 1.42/0.58  fof(f19,negated_conjecture,(
% 1.42/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.42/0.58    inference(negated_conjecture,[],[f18])).
% 1.42/0.58  fof(f18,conjecture,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.42/0.58  fof(f74,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f30])).
% 1.42/0.58  fof(f30,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f11])).
% 1.42/0.58  fof(f11,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.58  fof(f165,plain,(
% 1.42/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0))) )),
% 1.42/0.58    inference(resolution,[],[f60,f56])).
% 1.42/0.58  fof(f56,plain,(
% 1.42/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f3])).
% 1.42/0.58  fof(f3,axiom,(
% 1.42/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.42/0.58  fof(f60,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f26])).
% 1.42/0.58  fof(f26,plain,(
% 1.42/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(flattening,[],[f25])).
% 1.42/0.58  fof(f25,plain,(
% 1.42/0.58    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(ennf_transformation,[],[f10])).
% 1.42/0.58  fof(f10,axiom,(
% 1.42/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.42/0.58  fof(f344,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0)))))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f343,f233])).
% 1.42/0.58  fof(f233,plain,(
% 1.42/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.42/0.58    inference(resolution,[],[f184,f74])).
% 1.42/0.58  fof(f184,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.42/0.58    inference(forward_demodulation,[],[f183,f179])).
% 1.42/0.58  fof(f179,plain,(
% 1.42/0.58    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f176,f50])).
% 1.42/0.58  fof(f50,plain,(
% 1.42/0.58    v1_funct_1(sK3)),
% 1.42/0.58    inference(cnf_transformation,[],[f42])).
% 1.42/0.58  fof(f176,plain,(
% 1.42/0.58    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.42/0.58    inference(resolution,[],[f84,f52])).
% 1.42/0.58  fof(f84,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f38])).
% 1.42/0.58  fof(f38,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.42/0.58    inference(flattening,[],[f37])).
% 1.42/0.58  fof(f37,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.42/0.58    inference(ennf_transformation,[],[f16])).
% 1.42/0.58  fof(f16,axiom,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.42/0.58  fof(f183,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f180,f50])).
% 1.42/0.58  fof(f180,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.42/0.58    inference(resolution,[],[f86,f52])).
% 1.42/0.58  fof(f86,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f40])).
% 1.42/0.58  fof(f40,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.42/0.58    inference(flattening,[],[f39])).
% 1.42/0.58  fof(f39,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.42/0.58    inference(ennf_transformation,[],[f15])).
% 1.42/0.58  fof(f15,axiom,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.42/0.58  fof(f343,plain,(
% 1.42/0.58    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0)))))) )),
% 1.42/0.58    inference(forward_demodulation,[],[f342,f179])).
% 1.42/0.58  fof(f342,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0))))) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.42/0.58    inference(forward_demodulation,[],[f338,f179])).
% 1.42/0.58  fof(f338,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)),k2_relat_1(k2_partfun1(sK0,sK1,sK3,X0))))) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.42/0.58    inference(resolution,[],[f175,f174])).
% 1.42/0.58  fof(f174,plain,(
% 1.42/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f171,f50])).
% 1.42/0.58  fof(f171,plain,(
% 1.42/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.42/0.58    inference(resolution,[],[f85,f52])).
% 1.42/0.58  fof(f85,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f40])).
% 1.42/0.58  fof(f175,plain,(
% 1.42/0.58    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.42/0.58    inference(resolution,[],[f65,f87])).
% 1.42/0.58  fof(f87,plain,(
% 1.42/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.58    inference(equality_resolution,[],[f67])).
% 1.42/0.58  fof(f67,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.58    inference(cnf_transformation,[],[f45])).
% 1.42/0.58  fof(f45,plain,(
% 1.42/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.58    inference(flattening,[],[f44])).
% 1.42/0.58  fof(f44,plain,(
% 1.42/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.58    inference(nnf_transformation,[],[f1])).
% 1.42/0.58  fof(f1,axiom,(
% 1.42/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.58  fof(f65,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f29])).
% 1.42/0.58  fof(f29,plain,(
% 1.42/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(flattening,[],[f28])).
% 1.42/0.58  fof(f28,plain,(
% 1.42/0.58    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.42/0.58    inference(ennf_transformation,[],[f17])).
% 1.42/0.58  fof(f17,axiom,(
% 1.42/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.42/0.58  fof(f528,plain,(
% 1.42/0.58    ( ! [X2] : (k1_xboole_0 = k1_relset_1(X2,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0))) )),
% 1.42/0.58    inference(forward_demodulation,[],[f519,f310])).
% 1.42/0.58  fof(f519,plain,(
% 1.42/0.58    ( ! [X2] : (k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_relset_1(X2,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0))) )),
% 1.42/0.58    inference(resolution,[],[f432,f169])).
% 1.42/0.58  fof(f169,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X1) = k1_relset_1(X0,k1_xboole_0,X1)) )),
% 1.42/0.58    inference(superposition,[],[f75,f89])).
% 1.42/0.58  fof(f89,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.42/0.58    inference(equality_resolution,[],[f73])).
% 1.42/0.58  fof(f73,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.42/0.58    inference(cnf_transformation,[],[f48])).
% 1.42/0.58  fof(f75,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f31])).
% 1.42/0.58  fof(f31,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f13])).
% 1.42/0.58  fof(f13,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.42/0.58  fof(f2021,plain,(
% 1.42/0.58    sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | spl4_28)),
% 1.42/0.58    inference(forward_demodulation,[],[f2020,f1955])).
% 1.42/0.58  fof(f1955,plain,(
% 1.42/0.58    k1_xboole_0 = sK1 | ~spl4_4),
% 1.42/0.58    inference(global_subsumption,[],[f111])).
% 1.42/0.58  fof(f111,plain,(
% 1.42/0.58    k1_xboole_0 = sK1 | ~spl4_4),
% 1.42/0.58    inference(avatar_component_clause,[],[f110])).
% 1.42/0.58  fof(f110,plain,(
% 1.42/0.58    spl4_4 <=> k1_xboole_0 = sK1),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.42/0.58  fof(f2020,plain,(
% 1.42/0.58    sK0 != k1_relset_1(sK0,sK1,k1_xboole_0) | (~spl4_4 | spl4_28)),
% 1.42/0.58    inference(forward_demodulation,[],[f630,f1972])).
% 1.42/0.58  fof(f1972,plain,(
% 1.42/0.58    k1_xboole_0 = sK3 | ~spl4_4),
% 1.42/0.58    inference(subsumption_resolution,[],[f1971,f56])).
% 1.42/0.58  fof(f1971,plain,(
% 1.42/0.58    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3 | ~spl4_4),
% 1.42/0.58    inference(forward_demodulation,[],[f1970,f89])).
% 1.42/0.58  fof(f1970,plain,(
% 1.42/0.58    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3) | k1_xboole_0 = sK3 | ~spl4_4),
% 1.42/0.58    inference(forward_demodulation,[],[f1969,f1955])).
% 1.42/0.58  fof(f1969,plain,(
% 1.42/0.58    k1_xboole_0 = sK3 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) | ~spl4_4),
% 1.42/0.58    inference(forward_demodulation,[],[f1968,f89])).
% 1.42/0.58  fof(f1968,plain,(
% 1.42/0.58    sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) | ~spl4_4),
% 1.42/0.58    inference(forward_demodulation,[],[f1536,f1955])).
% 1.42/0.58  fof(f1536,plain,(
% 1.42/0.58    sK3 = k2_zfmisc_1(k1_relat_1(sK3),sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 1.42/0.58    inference(resolution,[],[f550,f68])).
% 1.42/0.58  fof(f68,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f45])).
% 1.42/0.58  fof(f550,plain,(
% 1.42/0.58    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1))),
% 1.42/0.58    inference(resolution,[],[f202,f69])).
% 1.42/0.58  fof(f202,plain,(
% 1.42/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 1.42/0.58    inference(subsumption_resolution,[],[f201,f140])).
% 1.42/0.58  fof(f201,plain,(
% 1.42/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | ~v1_relat_1(sK3)),
% 1.42/0.58    inference(subsumption_resolution,[],[f195,f50])).
% 1.42/0.58  fof(f195,plain,(
% 1.42/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.42/0.58    inference(resolution,[],[f194,f65])).
% 1.42/0.58  fof(f194,plain,(
% 1.42/0.58    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.42/0.58    inference(subsumption_resolution,[],[f193,f140])).
% 1.42/0.58  fof(f193,plain,(
% 1.42/0.58    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.42/0.58    inference(resolution,[],[f156,f61])).
% 1.42/0.58  fof(f61,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f43])).
% 1.42/0.58  fof(f43,plain,(
% 1.42/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(nnf_transformation,[],[f27])).
% 1.42/0.58  fof(f27,plain,(
% 1.42/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(ennf_transformation,[],[f7])).
% 1.42/0.58  fof(f7,axiom,(
% 1.42/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.42/0.58  fof(f156,plain,(
% 1.42/0.58    v5_relat_1(sK3,sK1)),
% 1.42/0.58    inference(resolution,[],[f76,f52])).
% 1.42/0.58  fof(f76,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f32])).
% 1.42/0.58  fof(f32,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f20])).
% 1.42/0.58  fof(f20,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.42/0.58    inference(pure_predicate_removal,[],[f12])).
% 1.42/0.58  fof(f12,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.42/0.58  fof(f630,plain,(
% 1.42/0.58    sK0 != k1_relset_1(sK0,sK1,sK3) | spl4_28),
% 1.42/0.58    inference(avatar_component_clause,[],[f629])).
% 1.42/0.58  fof(f629,plain,(
% 1.42/0.58    spl4_28 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.42/0.58  fof(f1953,plain,(
% 1.42/0.58    spl4_3 | ~spl4_28),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f1952])).
% 1.42/0.58  fof(f1952,plain,(
% 1.42/0.58    $false | (spl4_3 | ~spl4_28)),
% 1.42/0.58    inference(subsumption_resolution,[],[f1944,f246])).
% 1.42/0.58  fof(f246,plain,(
% 1.42/0.58    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.42/0.58    inference(superposition,[],[f107,f179])).
% 1.42/0.58  fof(f107,plain,(
% 1.42/0.58    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.42/0.58    inference(avatar_component_clause,[],[f105])).
% 1.42/0.58  fof(f105,plain,(
% 1.42/0.58    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.42/0.58  fof(f1944,plain,(
% 1.42/0.58    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_28),
% 1.42/0.58    inference(superposition,[],[f413,f903])).
% 1.42/0.58  fof(f903,plain,(
% 1.42/0.58    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_28),
% 1.42/0.58    inference(resolution,[],[f739,f53])).
% 1.42/0.58  fof(f53,plain,(
% 1.42/0.58    r1_tarski(sK2,sK0)),
% 1.42/0.58    inference(cnf_transformation,[],[f42])).
% 1.42/0.58  fof(f739,plain,(
% 1.42/0.58    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_28),
% 1.42/0.58    inference(subsumption_resolution,[],[f738,f140])).
% 1.42/0.58  fof(f738,plain,(
% 1.42/0.58    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl4_28),
% 1.42/0.58    inference(superposition,[],[f60,f734])).
% 1.42/0.58  fof(f734,plain,(
% 1.42/0.58    sK0 = k1_relat_1(sK3) | ~spl4_28),
% 1.42/0.58    inference(superposition,[],[f631,f168])).
% 1.42/0.58  fof(f168,plain,(
% 1.42/0.58    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.42/0.58    inference(resolution,[],[f75,f52])).
% 1.42/0.58  fof(f631,plain,(
% 1.42/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_28),
% 1.42/0.58    inference(avatar_component_clause,[],[f629])).
% 1.42/0.58  fof(f413,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f412,f233])).
% 1.42/0.58  fof(f412,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f406,f248])).
% 1.42/0.58  fof(f248,plain,(
% 1.42/0.58    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.42/0.58    inference(superposition,[],[f174,f179])).
% 1.42/0.58  fof(f406,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) | ~v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.42/0.58    inference(resolution,[],[f358,f65])).
% 1.42/0.58  fof(f358,plain,(
% 1.42/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f357,f233])).
% 1.42/0.58  fof(f357,plain,(
% 1.42/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.42/0.58    inference(resolution,[],[f235,f61])).
% 1.42/0.58  fof(f235,plain,(
% 1.42/0.58    ( ! [X2] : (v5_relat_1(k7_relat_1(sK3,X2),sK1)) )),
% 1.42/0.58    inference(resolution,[],[f184,f76])).
% 1.42/0.58  fof(f1823,plain,(
% 1.42/0.58    spl4_2 | ~spl4_28),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f1822])).
% 1.42/0.58  fof(f1822,plain,(
% 1.42/0.58    $false | (spl4_2 | ~spl4_28)),
% 1.42/0.58    inference(subsumption_resolution,[],[f1818,f247])).
% 1.42/0.58  fof(f247,plain,(
% 1.42/0.58    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.42/0.58    inference(superposition,[],[f103,f179])).
% 1.42/0.58  fof(f103,plain,(
% 1.42/0.58    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.42/0.58    inference(avatar_component_clause,[],[f101])).
% 1.42/0.58  fof(f101,plain,(
% 1.42/0.58    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.42/0.58  fof(f1818,plain,(
% 1.42/0.58    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_28),
% 1.42/0.58    inference(superposition,[],[f415,f903])).
% 1.42/0.58  fof(f415,plain,(
% 1.42/0.58    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f414,f233])).
% 1.42/0.58  fof(f414,plain,(
% 1.42/0.58    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f407,f248])).
% 1.42/0.58  fof(f407,plain,(
% 1.42/0.58    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) | ~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.42/0.58    inference(resolution,[],[f358,f64])).
% 1.42/0.58  fof(f64,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f29])).
% 1.42/0.58  fof(f632,plain,(
% 1.42/0.58    spl4_28 | spl4_4),
% 1.42/0.58    inference(avatar_split_clause,[],[f188,f110,f629])).
% 1.42/0.58  fof(f188,plain,(
% 1.42/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.42/0.58    inference(subsumption_resolution,[],[f185,f51])).
% 1.42/0.58  fof(f51,plain,(
% 1.42/0.58    v1_funct_2(sK3,sK0,sK1)),
% 1.42/0.58    inference(cnf_transformation,[],[f42])).
% 1.42/0.58  fof(f185,plain,(
% 1.42/0.58    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.42/0.58    inference(resolution,[],[f77,f52])).
% 1.42/0.58  fof(f77,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f49])).
% 1.42/0.58  fof(f49,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(nnf_transformation,[],[f34])).
% 1.42/0.58  fof(f34,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(flattening,[],[f33])).
% 1.42/0.58  fof(f33,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f14])).
% 1.42/0.58  fof(f14,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.42/0.58  fof(f230,plain,(
% 1.42/0.58    spl4_1),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f229])).
% 1.42/0.58  fof(f229,plain,(
% 1.42/0.58    $false | spl4_1),
% 1.42/0.58    inference(resolution,[],[f174,f99])).
% 1.42/0.58  fof(f99,plain,(
% 1.42/0.58    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.42/0.58    inference(avatar_component_clause,[],[f97])).
% 1.42/0.58  fof(f97,plain,(
% 1.42/0.58    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.42/0.58  fof(f117,plain,(
% 1.42/0.58    ~spl4_4 | spl4_5),
% 1.42/0.58    inference(avatar_split_clause,[],[f54,f114,f110])).
% 1.42/0.58  fof(f54,plain,(
% 1.42/0.58    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.42/0.58    inference(cnf_transformation,[],[f42])).
% 1.42/0.58  fof(f108,plain,(
% 1.42/0.58    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.42/0.58    inference(avatar_split_clause,[],[f55,f105,f101,f97])).
% 1.42/0.58  fof(f55,plain,(
% 1.42/0.58    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.42/0.58    inference(cnf_transformation,[],[f42])).
% 1.42/0.58  % SZS output end Proof for theBenchmark
% 1.42/0.58  % (29315)------------------------------
% 1.42/0.58  % (29315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (29315)Termination reason: Refutation
% 1.42/0.58  
% 1.42/0.58  % (29315)Memory used [KB]: 11769
% 1.42/0.58  % (29315)Time elapsed: 0.158 s
% 1.42/0.58  % (29315)------------------------------
% 1.42/0.58  % (29315)------------------------------
% 1.42/0.59  % (29304)Success in time 0.223 s
%------------------------------------------------------------------------------

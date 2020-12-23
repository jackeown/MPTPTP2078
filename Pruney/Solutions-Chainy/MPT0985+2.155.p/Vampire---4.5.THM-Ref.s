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
% DateTime   : Thu Dec  3 13:02:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  201 (1230 expanded)
%              Number of leaves         :   25 ( 321 expanded)
%              Depth                    :   20
%              Number of atoms          :  615 (6413 expanded)
%              Number of equality atoms :  126 (1006 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f101,f109,f113,f146,f292,f302,f352,f521,f1287,f1301])).

fof(f1301,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f1300])).

fof(f1300,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1299,f1035])).

fof(f1035,plain,
    ( ! [X1] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X1)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1034,f669])).

fof(f669,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f627,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f627,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(superposition,[],[f125,f347])).

fof(f347,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl3_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f125,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f124,f44])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).

fof(f34,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f124,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1034,plain,
    ( ! [X1] : v1_funct_2(k2_funct_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X1)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1033,f625])).

fof(f625,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_19 ),
    inference(superposition,[],[f119,f347])).

fof(f119,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f118,f110])).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f106,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f118,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1033,plain,
    ( ! [X1] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1032,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1032,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1031,f892])).

fof(f892,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f891,f890])).

fof(f890,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f888,f347])).

fof(f888,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f285,f490])).

fof(f490,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK2,X0)
    | ~ spl3_7 ),
    inference(resolution,[],[f323,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f323,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f200,f145])).

fof(f200,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK2,X1),sK1) ),
    inference(forward_demodulation,[],[f190,f129])).

fof(f129,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f71,f42])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f190,plain,(
    ! [X1] : r1_tarski(k7_relset_1(sK0,sK1,sK2,X1),sK1) ),
    inference(resolution,[],[f127,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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

fof(f127,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f70,f42])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f285,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f284,f110])).

fof(f284,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f257,f40])).

fof(f257,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f134,f43])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k9_relat_1(X0,k1_xboole_0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f891,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f889,f347])).

fof(f889,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f282,f490])).

fof(f282,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f281,f110])).

fof(f281,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f258,f40])).

fof(f258,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f135,f43])).

fof(f135,plain,(
    ! [X1] :
      ( ~ v2_funct_1(X1)
      | k1_relat_1(X1) = k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1031,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1) )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1030,f621])).

fof(f621,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(superposition,[],[f100,f347])).

fof(f100,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1030,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1)
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1023,f624])).

fof(f624,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_19 ),
    inference(superposition,[],[f114,f347])).

fof(f114,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f102,f110])).

fof(f102,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1023,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1)
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl3_19 ),
    inference(superposition,[],[f54,f626])).

fof(f626,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_19 ),
    inference(superposition,[],[f122,f347])).

fof(f122,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f110])).

fof(f121,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1299,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1298,f347])).

fof(f1298,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f86,f145])).

fof(f86,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1287,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f1275])).

fof(f1275,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(resolution,[],[f1029,f668])).

fof(f668,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f620,f145])).

fof(f620,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3
    | ~ spl3_19 ),
    inference(superposition,[],[f90,f347])).

fof(f90,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1029,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1028,f669])).

fof(f1028,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1027,f625])).

fof(f1027,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1026,f46])).

fof(f1026,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0))) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1025,f892])).

fof(f1025,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0))) )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1024,f621])).

fof(f1024,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0)))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1022,f624])).

fof(f1022,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0)))
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) )
    | ~ spl3_19 ),
    inference(superposition,[],[f55,f626])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f521,plain,
    ( spl3_6
    | ~ spl3_7
    | spl3_19
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | spl3_6
    | ~ spl3_7
    | spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f519,f346])).

fof(f346,plain,
    ( k1_xboole_0 != sK2
    | spl3_19 ),
    inference(avatar_component_clause,[],[f345])).

fof(f519,plain,
    ( k1_xboole_0 = sK2
    | spl3_6
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f518,f374])).

fof(f374,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_6
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f373,f351])).

fof(f351,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl3_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f373,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f310,f317])).

fof(f317,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f126,f145])).

fof(f126,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f310,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f140,f145])).

fof(f140,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_6
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f518,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f509,f327])).

fof(f327,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f304,f145])).

fof(f304,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f303,f125])).

fof(f303,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f253,f110])).

fof(f253,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f123,f40])).

fof(f123,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f54,f72])).

fof(f509,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(resolution,[],[f364,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f364,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f294,f145])).

fof(f294,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(forward_demodulation,[],[f293,f125])).

fof(f293,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f255,f110])).

fof(f255,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f128,f40])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f72])).

fof(f352,plain,
    ( spl3_19
    | spl3_20
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f343,f143,f349,f345])).

fof(f343,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f334,f311])).

fof(f311,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f41,f145])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f334,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(resolution,[],[f312,f76])).

fof(f312,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f42,f145])).

fof(f302,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f300,f86])).

fof(f300,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f299,f125])).

fof(f299,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f298,f119])).

fof(f298,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f297,f187])).

fof(f187,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(superposition,[],[f126,f141])).

fof(f141,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f297,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f296,f122])).

fof(f296,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f254,f100])).

fof(f254,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f123,f114])).

fof(f292,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f290,f90])).

fof(f290,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f289,f125])).

fof(f289,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0)))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f288,f119])).

fof(f288,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f287,f187])).

fof(f287,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f286,f122])).

fof(f286,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f256,f100])).

fof(f256,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f128,f114])).

fof(f146,plain,
    ( spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f137,f143,f139])).

fof(f137,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f136,f41])).

fof(f136,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f64,f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f113,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f111,f110])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f102,f82])).

fof(f82,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f109,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f107,f52])).

fof(f107,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f106,f96])).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f101,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f92,f98,f94])).

fof(f92,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f88,f84,f80])).

fof(f45,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (28405)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  % (28421)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.49  % (28406)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (28408)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (28399)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (28400)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (28417)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (28401)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (28402)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (28415)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (28416)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (28409)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (28407)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (28399)Refutation not found, incomplete strategy% (28399)------------------------------
% 0.20/0.53  % (28399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28399)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28399)Memory used [KB]: 10746
% 0.20/0.53  % (28399)Time elapsed: 0.100 s
% 0.20/0.53  % (28399)------------------------------
% 0.20/0.53  % (28399)------------------------------
% 0.20/0.53  % (28403)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (28419)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (28414)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (28398)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (28418)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (28423)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (28411)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (28408)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1302,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f91,f101,f109,f113,f146,f292,f302,f352,f521,f1287,f1301])).
% 0.20/0.54  fof(f1301,plain,(
% 0.20/0.54    spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_19),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1300])).
% 0.20/0.54  fof(f1300,plain,(
% 0.20/0.54    $false | (spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1299,f1035])).
% 0.20/0.54  fof(f1035,plain,(
% 0.20/0.54    ( ! [X1] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X1)) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f1034,f669])).
% 0.20/0.54  fof(f669,plain,(
% 0.20/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f627,f145])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl3_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f143])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    spl3_7 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.54  fof(f627,plain,(
% 0.20/0.54    sK1 = k2_relat_1(k1_xboole_0) | ~spl3_19),
% 0.20/0.54    inference(superposition,[],[f125,f347])).
% 0.20/0.54  fof(f347,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl3_19),
% 0.20/0.54    inference(avatar_component_clause,[],[f345])).
% 0.20/0.54  fof(f345,plain,(
% 0.20/0.54    spl3_19 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    sK1 = k2_relat_1(sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f124,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f15])).
% 0.20/0.54  fof(f15,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f62,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f1034,plain,(
% 0.20/0.54    ( ! [X1] : (v1_funct_2(k2_funct_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X1)) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f1033,f625])).
% 0.20/0.54  fof(f625,plain,(
% 0.20/0.54    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_19),
% 0.20/0.54    inference(superposition,[],[f119,f347])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f118,f110])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f106,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f47,f42])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f117,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f50,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    v2_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.54  fof(f1033,plain,(
% 0.20/0.54    ( ! [X1] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1)) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1032,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.54  fof(f1032,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1)) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f1031,f892])).
% 0.20/0.54  fof(f892,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f891,f890])).
% 0.20/0.54  fof(f890,plain,(
% 0.20/0.54    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f888,f347])).
% 0.20/0.54  fof(f888,plain,(
% 0.20/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_7),
% 0.20/0.54    inference(superposition,[],[f285,f490])).
% 0.20/0.54  fof(f490,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK2,X0)) ) | ~spl3_7),
% 0.20/0.54    inference(resolution,[],[f323,f115])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f59,f46])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f323,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k1_xboole_0)) ) | ~spl3_7),
% 0.20/0.54    inference(superposition,[],[f200,f145])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,X1),sK1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f190,f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 0.20/0.54    inference(resolution,[],[f71,f42])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(k7_relset_1(sK0,sK1,sK2,X1),sK1)) )),
% 0.20/0.54    inference(resolution,[],[f127,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK1))) )),
% 0.20/0.54    inference(resolution,[],[f70,f42])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f284,f110])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f257,f40])).
% 0.20/0.54  fof(f257,plain,(
% 0.20/0.54    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f134,f43])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_xboole_0 = k10_relat_1(X0,k9_relat_1(X0,k1_xboole_0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(resolution,[],[f56,f46])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.54  fof(f891,plain,(
% 0.20/0.54    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl3_7 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f889,f347])).
% 0.20/0.54  fof(f889,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0) | ~spl3_7),
% 0.20/0.54    inference(superposition,[],[f282,f490])).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f281,f110])).
% 0.20/0.54  fof(f281,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f258,f40])).
% 0.20/0.54  fof(f258,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f135,f43])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    ( ! [X1] : (~v2_funct_1(X1) | k1_relat_1(X1) = k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(resolution,[],[f56,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f1031,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1)) ) | (~spl3_5 | ~spl3_19)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1030,f621])).
% 0.20/0.54  fof(f621,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_5 | ~spl3_19)),
% 0.20/0.54    inference(superposition,[],[f100,f347])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f98])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.54  fof(f1030,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | ~spl3_19),
% 0.20/0.54    inference(subsumption_resolution,[],[f1023,f624])).
% 0.20/0.54  fof(f624,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl3_19),
% 0.20/0.54    inference(superposition,[],[f114,f347])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f102,f110])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f49,f40])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.54  fof(f1023,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),X1) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | ~spl3_19),
% 0.20/0.55    inference(superposition,[],[f54,f626])).
% 0.20/0.55  fof(f626,plain,(
% 0.20/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_19),
% 0.20/0.55    inference(superposition,[],[f122,f347])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f121,f110])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f120,f40])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(resolution,[],[f51,f43])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.55  fof(f1299,plain,(
% 0.20/0.55    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(forward_demodulation,[],[f1298,f347])).
% 0.20/0.55  fof(f1298,plain,(
% 0.20/0.55    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f86,f145])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f1287,plain,(
% 0.20/0.55    spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_19),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f1275])).
% 0.20/0.55  fof(f1275,plain,(
% 0.20/0.55    $false | (spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(resolution,[],[f1029,f668])).
% 0.20/0.55  fof(f668,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(forward_demodulation,[],[f620,f145])).
% 0.20/0.55  fof(f620,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_3 | ~spl3_19)),
% 0.20/0.55    inference(superposition,[],[f90,f347])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.55  fof(f1029,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(forward_demodulation,[],[f1028,f669])).
% 0.20/0.55  fof(f1028,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(forward_demodulation,[],[f1027,f625])).
% 0.20/0.55  fof(f1027,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1026,f46])).
% 0.20/0.55  fof(f1026,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.20/0.55    inference(forward_demodulation,[],[f1025,f892])).
% 0.20/0.55  fof(f1025,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0)))) ) | (~spl3_5 | ~spl3_19)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1024,f621])).
% 0.20/0.55  fof(f1024,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0))) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | ~spl3_19),
% 0.20/0.55    inference(subsumption_resolution,[],[f1022,f624])).
% 0.20/0.55  fof(f1022,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),X0))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0))) ) | ~spl3_19),
% 0.20/0.55    inference(superposition,[],[f55,f626])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f521,plain,(
% 0.20/0.55    spl3_6 | ~spl3_7 | spl3_19 | ~spl3_20),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f520])).
% 0.20/0.55  fof(f520,plain,(
% 0.20/0.55    $false | (spl3_6 | ~spl3_7 | spl3_19 | ~spl3_20)),
% 0.20/0.55    inference(subsumption_resolution,[],[f519,f346])).
% 0.20/0.55  fof(f346,plain,(
% 0.20/0.55    k1_xboole_0 != sK2 | spl3_19),
% 0.20/0.55    inference(avatar_component_clause,[],[f345])).
% 0.20/0.55  fof(f519,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | (spl3_6 | ~spl3_7 | ~spl3_20)),
% 0.20/0.55    inference(subsumption_resolution,[],[f518,f374])).
% 0.20/0.55  fof(f374,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relat_1(sK2) | (spl3_6 | ~spl3_7 | ~spl3_20)),
% 0.20/0.55    inference(forward_demodulation,[],[f373,f351])).
% 0.20/0.55  fof(f351,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl3_20),
% 0.20/0.55    inference(avatar_component_clause,[],[f349])).
% 0.20/0.55  fof(f349,plain,(
% 0.20/0.55    spl3_20 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.55  fof(f373,plain,(
% 0.20/0.55    sK0 != k1_relat_1(sK2) | (spl3_6 | ~spl3_7)),
% 0.20/0.55    inference(superposition,[],[f310,f317])).
% 0.20/0.55  fof(f317,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl3_7),
% 0.20/0.55    inference(superposition,[],[f126,f145])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    inference(resolution,[],[f63,f42])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f310,plain,(
% 0.20/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl3_6 | ~spl3_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f140,f145])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    sK0 != k1_relset_1(sK0,sK1,sK2) | spl3_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f139])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    spl3_6 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.55  fof(f518,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_7),
% 0.20/0.55    inference(subsumption_resolution,[],[f509,f327])).
% 0.20/0.55  fof(f327,plain,(
% 0.20/0.55    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl3_7),
% 0.20/0.55    inference(superposition,[],[f304,f145])).
% 0.20/0.55  fof(f304,plain,(
% 0.20/0.55    v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.20/0.55    inference(forward_demodulation,[],[f303,f125])).
% 0.20/0.55  fof(f303,plain,(
% 0.20/0.55    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f253,f110])).
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(resolution,[],[f123,f40])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(resolution,[],[f54,f72])).
% 0.20/0.55  fof(f509,plain,(
% 0.20/0.55    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_7),
% 0.20/0.55    inference(resolution,[],[f364,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.55    inference(equality_resolution,[],[f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f364,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl3_7),
% 0.20/0.55    inference(superposition,[],[f294,f145])).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.20/0.55    inference(forward_demodulation,[],[f293,f125])).
% 0.20/0.55  fof(f293,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.55    inference(subsumption_resolution,[],[f255,f110])).
% 0.20/0.55  fof(f255,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(resolution,[],[f128,f40])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(resolution,[],[f55,f72])).
% 0.20/0.55  fof(f352,plain,(
% 0.20/0.55    spl3_19 | spl3_20 | ~spl3_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f343,f143,f349,f345])).
% 0.20/0.55  fof(f343,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_7),
% 0.20/0.55    inference(subsumption_resolution,[],[f334,f311])).
% 0.20/0.55  fof(f311,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl3_7),
% 0.20/0.55    inference(superposition,[],[f41,f145])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f334,plain,(
% 0.20/0.55    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_7),
% 0.20/0.55    inference(resolution,[],[f312,f76])).
% 0.20/0.55  fof(f312,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_7),
% 0.20/0.55    inference(superposition,[],[f42,f145])).
% 0.20/0.55  fof(f302,plain,(
% 0.20/0.55    spl3_2 | ~spl3_5 | ~spl3_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f301])).
% 0.20/0.55  fof(f301,plain,(
% 0.20/0.55    $false | (spl3_2 | ~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f300,f86])).
% 0.20/0.55  fof(f300,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f299,f125])).
% 0.20/0.55  fof(f299,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) | (~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f298,f119])).
% 0.20/0.55  fof(f298,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f297,f187])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | ~spl3_6),
% 0.20/0.55    inference(superposition,[],[f126,f141])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f139])).
% 0.20/0.55  fof(f297,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~spl3_5),
% 0.20/0.55    inference(forward_demodulation,[],[f296,f122])).
% 0.20/0.55  fof(f296,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_5),
% 0.20/0.55    inference(subsumption_resolution,[],[f254,f100])).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    inference(resolution,[],[f123,f114])).
% 0.20/0.55  fof(f292,plain,(
% 0.20/0.55    spl3_3 | ~spl3_5 | ~spl3_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f291])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    $false | (spl3_3 | ~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f290,f90])).
% 0.20/0.55  fof(f290,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f289,f125])).
% 0.20/0.55  fof(f289,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0))) | (~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f288,f119])).
% 0.20/0.55  fof(f288,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_5 | ~spl3_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f287,f187])).
% 0.20/0.55  fof(f287,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~spl3_5),
% 0.20/0.55    inference(forward_demodulation,[],[f286,f122])).
% 0.20/0.55  fof(f286,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_5),
% 0.20/0.55    inference(subsumption_resolution,[],[f256,f100])).
% 0.20/0.55  fof(f256,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    inference(resolution,[],[f128,f114])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    spl3_6 | spl3_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f137,f143,f139])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f136,f41])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    inference(resolution,[],[f64,f42])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl3_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    $false | spl3_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f111,f110])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f102,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl3_4),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    $false | spl3_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f107,f52])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f106,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    spl3_4 <=> v1_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ~spl3_4 | spl3_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f92,f98,f94])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(resolution,[],[f48,f40])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f45,f88,f84,f80])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (28408)------------------------------
% 0.20/0.55  % (28408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28408)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (28408)Memory used [KB]: 11385
% 0.20/0.55  % (28408)Time elapsed: 0.117 s
% 0.20/0.55  % (28408)------------------------------
% 0.20/0.55  % (28408)------------------------------
% 0.20/0.55  % (28410)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.55  % (28413)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.54/0.55  % (28397)Success in time 0.194 s
%------------------------------------------------------------------------------

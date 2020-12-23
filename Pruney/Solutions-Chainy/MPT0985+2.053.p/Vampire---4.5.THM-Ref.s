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
% DateTime   : Thu Dec  3 13:02:07 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  164 (1815 expanded)
%              Number of leaves         :   22 ( 478 expanded)
%              Depth                    :   15
%              Number of atoms          :  535 (10715 expanded)
%              Number of equality atoms :   95 (1490 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f189,f261,f263,f519,f525,f595,f611,f628,f1334,f1347])).

fof(f1347,plain,
    ( spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f1346])).

fof(f1346,plain,
    ( $false
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f1341,f825])).

fof(f825,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f824,f260])).

fof(f260,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f824,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f610,f254])).

fof(f254,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f610,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl7_24
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1341,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f629,f627,f802,f1340,f159])).

fof(f159,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f1340,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f1339,f829])).

fof(f829,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f640,f827])).

fof(f827,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f594,f260])).

fof(f594,plain,
    ( k1_xboole_0 = k4_relat_1(sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl7_22
  <=> k1_xboole_0 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f640,plain,
    ( k4_relat_1(k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f217,f260])).

fof(f217,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f89,f86,f186,f121])).

fof(f121,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f186,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f88,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f77])).

fof(f77,plain,
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

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
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

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f1339,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f1338,f260])).

fof(f1338,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f174,f254])).

fof(f174,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f802,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f750,f786])).

fof(f786,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f249,f260])).

fof(f249,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_4
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f750,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f646,f254])).

fof(f646,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1)))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f230,f260])).

fof(f230,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(forward_demodulation,[],[f214,f190])).

fof(f190,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f185,f90])).

fof(f90,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f185,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f88,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f214,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f86,f186,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f627,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl7_26
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f629,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f86,f260])).

fof(f1334,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f1333])).

fof(f1333,plain,
    ( $false
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f1326,f825])).

fof(f1326,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f629,f802,f856,f627,f158])).

fof(f158,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f856,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f774,f827])).

fof(f774,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f715,f254])).

fof(f715,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f520,f260])).

fof(f520,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_3 ),
    inference(forward_demodulation,[],[f178,f217])).

fof(f178,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f628,plain,
    ( spl7_26
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f305,f252,f625])).

fof(f305,plain,
    ( k1_xboole_0 != sK1
    | r1_tarski(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f304,f190])).

fof(f304,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f303,f186])).

fof(f303,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f235,f115])).

fof(f115,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f235,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f186,f184,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f184,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f88,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f611,plain,
    ( spl7_24
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f606,f252,f608])).

fof(f606,plain,
    ( k1_xboole_0 != sK1
    | v1_funct_2(sK2,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f605,f190])).

fof(f605,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f380,f186])).

fof(f380,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f231,f115])).

fof(f231,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f213,f190])).

fof(f213,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f86,f186,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f595,plain,
    ( spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f590,f248,f592])).

fof(f590,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f404,f229])).

fof(f229,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f215,f217])).

fof(f215,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f86,f186,f119])).

fof(f119,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f404,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k4_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[],[f113,f225])).

fof(f225,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f219,f217])).

fof(f219,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f89,f86,f186,f123])).

fof(f123,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f113,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f525,plain,
    ( ~ spl7_1
    | spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl7_1
    | spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f522,f289])).

fof(f289,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f288,f224])).

fof(f224,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f223,f217])).

fof(f223,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f218,f190])).

fof(f218,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f89,f86,f186,f122])).

fof(f122,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f288,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f282,f225])).

fof(f282,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f195,f229,f118])).

fof(f195,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f194,f186])).

fof(f194,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f193,f86])).

fof(f193,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f192,f89])).

fof(f192,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(superposition,[],[f169,f121])).

fof(f169,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f522,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1
    | spl7_3
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f195,f235,f250,f291,f520,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f291,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f290,f224])).

fof(f290,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f281,f225])).

fof(f281,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f195,f229,f117])).

fof(f250,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f248])).

fof(f519,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f516,f289])).

fof(f516,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f195,f235,f204,f250,f291,f144])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f204,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f203,f186])).

fof(f203,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f202,f86])).

fof(f202,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f197,f89])).

fof(f197,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_2 ),
    inference(superposition,[],[f174,f121])).

fof(f263,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f262,f252,f248])).

fof(f262,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f239,f186])).

fof(f239,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f114,f190])).

fof(f114,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f261,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f256,f252,f258])).

fof(f256,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f238,f186])).

fof(f238,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f113,f190])).

fof(f189,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f186,f180])).

fof(f180,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f86,f170,f120])).

fof(f120,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f170,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f168])).

fof(f179,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f91,f176,f172,f168])).

fof(f91,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31476)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (31460)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (31473)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (31461)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (31481)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (31463)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (31471)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.52  % (31468)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.52  % (31486)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.52  % (31477)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.53  % (31464)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (31462)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (31467)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (31488)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.53  % (31489)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.54  % (31482)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.54  % (31485)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (31479)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.54  % (31487)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (31465)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.54  % (31484)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.54  % (31478)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.54  % (31480)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (31469)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.54  % (31475)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (31470)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (31472)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.55  % (31477)Refutation not found, incomplete strategy% (31477)------------------------------
% 1.40/0.55  % (31477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (31477)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (31477)Memory used [KB]: 10746
% 1.40/0.55  % (31477)Time elapsed: 0.122 s
% 1.40/0.55  % (31477)------------------------------
% 1.40/0.55  % (31477)------------------------------
% 1.40/0.55  % (31466)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.55  % (31474)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.56  % (31483)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.59  % (31482)Refutation not found, incomplete strategy% (31482)------------------------------
% 1.40/0.59  % (31482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (31482)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.59  
% 1.40/0.59  % (31482)Memory used [KB]: 11129
% 1.40/0.59  % (31482)Time elapsed: 0.138 s
% 1.40/0.59  % (31482)------------------------------
% 1.40/0.59  % (31482)------------------------------
% 1.40/0.61  % (31486)Refutation found. Thanks to Tanya!
% 1.40/0.61  % SZS status Theorem for theBenchmark
% 1.40/0.63  % SZS output start Proof for theBenchmark
% 2.02/0.63  fof(f1348,plain,(
% 2.02/0.63    $false),
% 2.02/0.63    inference(avatar_sat_refutation,[],[f179,f189,f261,f263,f519,f525,f595,f611,f628,f1334,f1347])).
% 2.02/0.63  fof(f1347,plain,(
% 2.02/0.63    spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_22 | ~spl7_24 | ~spl7_26),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f1346])).
% 2.02/0.63  fof(f1346,plain,(
% 2.02/0.63    $false | (spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_22 | ~spl7_24 | ~spl7_26)),
% 2.02/0.63    inference(subsumption_resolution,[],[f1341,f825])).
% 2.02/0.63  fof(f825,plain,(
% 2.02/0.63    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_24)),
% 2.02/0.63    inference(forward_demodulation,[],[f824,f260])).
% 2.02/0.63  fof(f260,plain,(
% 2.02/0.63    k1_xboole_0 = sK2 | ~spl7_6),
% 2.02/0.63    inference(avatar_component_clause,[],[f258])).
% 2.02/0.63  fof(f258,plain,(
% 2.02/0.63    spl7_6 <=> k1_xboole_0 = sK2),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.02/0.63  fof(f824,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_5 | ~spl7_24)),
% 2.02/0.63    inference(forward_demodulation,[],[f610,f254])).
% 2.02/0.63  fof(f254,plain,(
% 2.02/0.63    k1_xboole_0 = sK1 | ~spl7_5),
% 2.02/0.63    inference(avatar_component_clause,[],[f252])).
% 2.02/0.63  fof(f252,plain,(
% 2.02/0.63    spl7_5 <=> k1_xboole_0 = sK1),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.02/0.63  fof(f610,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl7_24),
% 2.02/0.63    inference(avatar_component_clause,[],[f608])).
% 2.02/0.63  fof(f608,plain,(
% 2.02/0.63    spl7_24 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.02/0.63  fof(f1341,plain,(
% 2.02/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_22 | ~spl7_26)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f629,f627,f802,f1340,f159])).
% 2.02/0.63  fof(f159,plain,(
% 2.02/0.63    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(equality_resolution,[],[f145])).
% 2.02/0.63  fof(f145,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f76])).
% 2.02/0.63  fof(f76,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.02/0.63    inference(flattening,[],[f75])).
% 2.02/0.63  fof(f75,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.02/0.63    inference(ennf_transformation,[],[f35])).
% 2.02/0.63  fof(f35,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 2.02/0.63  fof(f1340,plain,(
% 2.02/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_22)),
% 2.02/0.63    inference(forward_demodulation,[],[f1339,f829])).
% 2.02/0.63  fof(f829,plain,(
% 2.02/0.63    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl7_6 | ~spl7_22)),
% 2.02/0.63    inference(backward_demodulation,[],[f640,f827])).
% 2.02/0.63  fof(f827,plain,(
% 2.02/0.63    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl7_6 | ~spl7_22)),
% 2.02/0.63    inference(forward_demodulation,[],[f594,f260])).
% 2.02/0.63  fof(f594,plain,(
% 2.02/0.63    k1_xboole_0 = k4_relat_1(sK2) | ~spl7_22),
% 2.02/0.63    inference(avatar_component_clause,[],[f592])).
% 2.02/0.63  fof(f592,plain,(
% 2.02/0.63    spl7_22 <=> k1_xboole_0 = k4_relat_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.02/0.63  fof(f640,plain,(
% 2.02/0.63    k4_relat_1(k1_xboole_0) = k2_funct_1(k1_xboole_0) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f217,f260])).
% 2.02/0.63  fof(f217,plain,(
% 2.02/0.63    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f89,f86,f186,f121])).
% 2.02/0.63  fof(f121,plain,(
% 2.02/0.63    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f55])).
% 2.02/0.63  fof(f55,plain,(
% 2.02/0.63    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f54])).
% 2.02/0.63  fof(f54,plain,(
% 2.02/0.63    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f19])).
% 2.02/0.63  fof(f19,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.02/0.63  fof(f186,plain,(
% 2.02/0.63    v1_relat_1(sK2)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f88,f136])).
% 2.02/0.63  fof(f136,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f69])).
% 2.02/0.63  fof(f69,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f28])).
% 2.02/0.63  fof(f28,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.02/0.63  fof(f88,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.63    inference(cnf_transformation,[],[f78])).
% 2.02/0.63  fof(f78,plain,(
% 2.02/0.63    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f77])).
% 2.02/0.63  fof(f77,plain,(
% 2.02/0.63    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f40,plain,(
% 2.02/0.63    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.02/0.63    inference(flattening,[],[f39])).
% 2.02/0.63  fof(f39,plain,(
% 2.02/0.63    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f37])).
% 2.02/0.63  fof(f37,negated_conjecture,(
% 2.02/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.02/0.63    inference(negated_conjecture,[],[f36])).
% 2.02/0.63  fof(f36,conjecture,(
% 2.02/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.02/0.63  fof(f86,plain,(
% 2.02/0.63    v1_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f78])).
% 2.02/0.63  fof(f89,plain,(
% 2.02/0.63    v2_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f78])).
% 2.02/0.63  fof(f1339,plain,(
% 2.02/0.63    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl7_2 | ~spl7_5 | ~spl7_6)),
% 2.02/0.63    inference(forward_demodulation,[],[f1338,f260])).
% 2.02/0.63  fof(f1338,plain,(
% 2.02/0.63    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl7_2 | ~spl7_5)),
% 2.02/0.63    inference(forward_demodulation,[],[f174,f254])).
% 2.02/0.63  fof(f174,plain,(
% 2.02/0.63    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl7_2),
% 2.02/0.63    inference(avatar_component_clause,[],[f172])).
% 2.02/0.63  fof(f172,plain,(
% 2.02/0.63    spl7_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.02/0.63  fof(f802,plain,(
% 2.02/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_5 | ~spl7_6)),
% 2.02/0.63    inference(backward_demodulation,[],[f750,f786])).
% 2.02/0.63  fof(f786,plain,(
% 2.02/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_4 | ~spl7_6)),
% 2.02/0.63    inference(forward_demodulation,[],[f249,f260])).
% 2.02/0.63  fof(f249,plain,(
% 2.02/0.63    k1_xboole_0 = k1_relat_1(sK2) | ~spl7_4),
% 2.02/0.63    inference(avatar_component_clause,[],[f248])).
% 2.02/0.63  fof(f248,plain,(
% 2.02/0.63    spl7_4 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.02/0.63  fof(f750,plain,(
% 2.02/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl7_5 | ~spl7_6)),
% 2.02/0.63    inference(backward_demodulation,[],[f646,f254])).
% 2.02/0.63  fof(f646,plain,(
% 2.02/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK1))) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f230,f260])).
% 2.02/0.63  fof(f230,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.02/0.63    inference(forward_demodulation,[],[f214,f190])).
% 2.02/0.63  fof(f190,plain,(
% 2.02/0.63    sK1 = k2_relat_1(sK2)),
% 2.02/0.63    inference(forward_demodulation,[],[f185,f90])).
% 2.02/0.63  fof(f90,plain,(
% 2.02/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f78])).
% 2.02/0.63  fof(f185,plain,(
% 2.02/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f88,f137])).
% 2.02/0.63  fof(f137,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f70])).
% 2.02/0.63  fof(f70,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f30])).
% 2.02/0.63  fof(f30,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.02/0.63  fof(f214,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f86,f186,f118])).
% 2.02/0.63  fof(f118,plain,(
% 2.02/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f51])).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f50])).
% 2.02/0.63  fof(f50,plain,(
% 2.02/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f34])).
% 2.02/0.63  fof(f34,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 2.02/0.63  fof(f627,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK0) | ~spl7_26),
% 2.02/0.63    inference(avatar_component_clause,[],[f625])).
% 2.02/0.63  fof(f625,plain,(
% 2.02/0.63    spl7_26 <=> r1_tarski(k1_xboole_0,sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.02/0.63  fof(f629,plain,(
% 2.02/0.63    v1_funct_1(k1_xboole_0) | ~spl7_6),
% 2.02/0.63    inference(backward_demodulation,[],[f86,f260])).
% 2.02/0.63  fof(f1334,plain,(
% 2.02/0.63    spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_22 | ~spl7_24 | ~spl7_26),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f1333])).
% 2.02/0.63  fof(f1333,plain,(
% 2.02/0.63    $false | (spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_22 | ~spl7_24 | ~spl7_26)),
% 2.02/0.63    inference(subsumption_resolution,[],[f1326,f825])).
% 2.02/0.63  fof(f1326,plain,(
% 2.02/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_22 | ~spl7_26)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f629,f802,f856,f627,f158])).
% 2.02/0.63  fof(f158,plain,(
% 2.02/0.63    ( ! [X2,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(equality_resolution,[],[f147])).
% 2.02/0.63  fof(f147,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f76])).
% 2.02/0.63  fof(f856,plain,(
% 2.02/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_22)),
% 2.02/0.63    inference(backward_demodulation,[],[f774,f827])).
% 2.02/0.63  fof(f774,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl7_3 | ~spl7_5 | ~spl7_6)),
% 2.02/0.63    inference(backward_demodulation,[],[f715,f254])).
% 2.02/0.63  fof(f715,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl7_3 | ~spl7_6)),
% 2.02/0.63    inference(backward_demodulation,[],[f520,f260])).
% 2.02/0.63  fof(f520,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_3),
% 2.02/0.63    inference(forward_demodulation,[],[f178,f217])).
% 2.02/0.63  fof(f178,plain,(
% 2.02/0.63    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_3),
% 2.02/0.63    inference(avatar_component_clause,[],[f176])).
% 2.02/0.63  fof(f176,plain,(
% 2.02/0.63    spl7_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.02/0.63  fof(f628,plain,(
% 2.02/0.63    spl7_26 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f305,f252,f625])).
% 2.02/0.63  fof(f305,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | r1_tarski(k1_xboole_0,sK0)),
% 2.02/0.63    inference(forward_demodulation,[],[f304,f190])).
% 2.02/0.63  fof(f304,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f303,f186])).
% 2.02/0.63  fof(f303,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f235,f115])).
% 2.02/0.63  fof(f115,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f79])).
% 2.02/0.63  fof(f79,plain,(
% 2.02/0.63    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(nnf_transformation,[],[f49])).
% 2.02/0.63  fof(f49,plain,(
% 2.02/0.63    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f14])).
% 2.02/0.63  fof(f14,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 2.02/0.63  fof(f235,plain,(
% 2.02/0.63    r1_tarski(k1_relat_1(sK2),sK0)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f186,f184,f128])).
% 2.02/0.63  fof(f128,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f80])).
% 2.02/0.63  fof(f80,plain,(
% 2.02/0.63    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(nnf_transformation,[],[f65])).
% 2.02/0.63  fof(f65,plain,(
% 2.02/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f7])).
% 2.02/0.63  fof(f7,axiom,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.02/0.63  fof(f184,plain,(
% 2.02/0.63    v4_relat_1(sK2,sK0)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f88,f138])).
% 2.02/0.63  fof(f138,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f71])).
% 2.02/0.63  fof(f71,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f38])).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.02/0.63    inference(pure_predicate_removal,[],[f29])).
% 2.02/0.63  fof(f29,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.02/0.63  fof(f611,plain,(
% 2.02/0.63    spl7_24 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f606,f252,f608])).
% 2.02/0.63  fof(f606,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | v1_funct_2(sK2,k1_xboole_0,sK1)),
% 2.02/0.63    inference(forward_demodulation,[],[f605,f190])).
% 2.02/0.63  fof(f605,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,sK1) | k1_xboole_0 != k2_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f380,f186])).
% 2.02/0.63  fof(f380,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_xboole_0,sK1) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f231,f115])).
% 2.02/0.63  fof(f231,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 2.02/0.63    inference(forward_demodulation,[],[f213,f190])).
% 2.02/0.63  fof(f213,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f86,f186,f117])).
% 2.02/0.63  fof(f117,plain,(
% 2.02/0.63    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f51])).
% 2.02/0.63  fof(f595,plain,(
% 2.02/0.63    spl7_22 | ~spl7_4),
% 2.02/0.63    inference(avatar_split_clause,[],[f590,f248,f592])).
% 2.02/0.63  fof(f590,plain,(
% 2.02/0.63    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k4_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f404,f229])).
% 2.02/0.63  fof(f229,plain,(
% 2.02/0.63    v1_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f215,f217])).
% 2.02/0.63  fof(f215,plain,(
% 2.02/0.63    v1_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f86,f186,f119])).
% 2.02/0.63  fof(f119,plain,(
% 2.02/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f53])).
% 2.02/0.63  fof(f53,plain,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f52])).
% 2.02/0.63  fof(f52,plain,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f20])).
% 2.02/0.63  fof(f20,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.02/0.63  fof(f404,plain,(
% 2.02/0.63    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k4_relat_1(sK2) | ~v1_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(superposition,[],[f113,f225])).
% 2.02/0.63  fof(f225,plain,(
% 2.02/0.63    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(backward_demodulation,[],[f219,f217])).
% 2.02/0.63  fof(f219,plain,(
% 2.02/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f89,f86,f186,f123])).
% 2.02/0.63  fof(f123,plain,(
% 2.02/0.63    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f57])).
% 2.02/0.63  fof(f57,plain,(
% 2.02/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f56])).
% 2.02/0.63  fof(f56,plain,(
% 2.02/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f26])).
% 2.02/0.63  fof(f26,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.02/0.63  fof(f113,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f48])).
% 2.02/0.63  fof(f48,plain,(
% 2.02/0.63    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f47])).
% 2.02/0.63  fof(f47,plain,(
% 2.02/0.63    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f13])).
% 2.02/0.63  fof(f13,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 2.02/0.63  fof(f525,plain,(
% 2.02/0.63    ~spl7_1 | spl7_3 | spl7_4),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f524])).
% 2.02/0.63  fof(f524,plain,(
% 2.02/0.63    $false | (~spl7_1 | spl7_3 | spl7_4)),
% 2.02/0.63    inference(subsumption_resolution,[],[f522,f289])).
% 2.02/0.63  fof(f289,plain,(
% 2.02/0.63    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f288,f224])).
% 2.02/0.63  fof(f224,plain,(
% 2.02/0.63    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 2.02/0.63    inference(backward_demodulation,[],[f223,f217])).
% 2.02/0.63  fof(f223,plain,(
% 2.02/0.63    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f218,f190])).
% 2.02/0.63  fof(f218,plain,(
% 2.02/0.63    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f89,f86,f186,f122])).
% 2.02/0.63  fof(f122,plain,(
% 2.02/0.63    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f57])).
% 2.02/0.63  fof(f288,plain,(
% 2.02/0.63    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f282,f225])).
% 2.02/0.63  fof(f282,plain,(
% 2.02/0.63    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) | ~spl7_1),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f195,f229,f118])).
% 2.02/0.63  fof(f195,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f194,f186])).
% 2.02/0.63  fof(f194,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f193,f86])).
% 2.02/0.63  fof(f193,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f192,f89])).
% 2.02/0.63  fof(f192,plain,(
% 2.02/0.63    v1_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 2.02/0.63    inference(superposition,[],[f169,f121])).
% 2.02/0.63  fof(f169,plain,(
% 2.02/0.63    v1_funct_1(k2_funct_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(avatar_component_clause,[],[f168])).
% 2.02/0.63  fof(f168,plain,(
% 2.02/0.63    spl7_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.02/0.63  fof(f522,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_1 | spl7_3 | spl7_4)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f195,f235,f250,f291,f520,f146])).
% 2.02/0.63  fof(f146,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f76])).
% 2.02/0.63  fof(f291,plain,(
% 2.02/0.63    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f290,f224])).
% 2.02/0.63  fof(f290,plain,(
% 2.02/0.63    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~spl7_1),
% 2.02/0.63    inference(forward_demodulation,[],[f281,f225])).
% 2.02/0.63  fof(f281,plain,(
% 2.02/0.63    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) | ~spl7_1),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f195,f229,f117])).
% 2.02/0.63  fof(f250,plain,(
% 2.02/0.63    k1_xboole_0 != k1_relat_1(sK2) | spl7_4),
% 2.02/0.63    inference(avatar_component_clause,[],[f248])).
% 2.02/0.63  fof(f519,plain,(
% 2.02/0.63    ~spl7_1 | spl7_2 | spl7_4),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f518])).
% 2.02/0.63  fof(f518,plain,(
% 2.02/0.63    $false | (~spl7_1 | spl7_2 | spl7_4)),
% 2.02/0.63    inference(subsumption_resolution,[],[f516,f289])).
% 2.02/0.63  fof(f516,plain,(
% 2.02/0.63    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_1 | spl7_2 | spl7_4)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f195,f235,f204,f250,f291,f144])).
% 2.02/0.63  fof(f144,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f76])).
% 2.02/0.63  fof(f204,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | spl7_2),
% 2.02/0.63    inference(subsumption_resolution,[],[f203,f186])).
% 2.02/0.63  fof(f203,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_relat_1(sK2) | spl7_2),
% 2.02/0.63    inference(subsumption_resolution,[],[f202,f86])).
% 2.02/0.63  fof(f202,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_2),
% 2.02/0.63    inference(subsumption_resolution,[],[f197,f89])).
% 2.02/0.63  fof(f197,plain,(
% 2.02/0.63    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_2),
% 2.02/0.63    inference(superposition,[],[f174,f121])).
% 2.02/0.63  fof(f263,plain,(
% 2.02/0.63    ~spl7_4 | spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f262,f252,f248])).
% 2.02/0.63  fof(f262,plain,(
% 2.02/0.63    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f239,f186])).
% 2.02/0.63  fof(f239,plain,(
% 2.02/0.63    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f114,f190])).
% 2.02/0.63  fof(f114,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f79])).
% 2.02/0.63  fof(f261,plain,(
% 2.02/0.63    spl7_6 | ~spl7_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f256,f252,f258])).
% 2.02/0.63  fof(f256,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 2.02/0.63    inference(subsumption_resolution,[],[f238,f186])).
% 2.02/0.63  fof(f238,plain,(
% 2.02/0.63    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 2.02/0.63    inference(superposition,[],[f113,f190])).
% 2.02/0.63  fof(f189,plain,(
% 2.02/0.63    spl7_1),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f188])).
% 2.02/0.63  fof(f188,plain,(
% 2.02/0.63    $false | spl7_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f186,f180])).
% 2.02/0.63  fof(f180,plain,(
% 2.02/0.63    ~v1_relat_1(sK2) | spl7_1),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f86,f170,f120])).
% 2.02/0.63  fof(f120,plain,(
% 2.02/0.63    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f53])).
% 2.02/0.63  fof(f170,plain,(
% 2.02/0.63    ~v1_funct_1(k2_funct_1(sK2)) | spl7_1),
% 2.02/0.63    inference(avatar_component_clause,[],[f168])).
% 2.02/0.63  fof(f179,plain,(
% 2.02/0.63    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 2.02/0.63    inference(avatar_split_clause,[],[f91,f176,f172,f168])).
% 2.02/0.63  fof(f91,plain,(
% 2.02/0.63    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.02/0.63    inference(cnf_transformation,[],[f78])).
% 2.02/0.63  % SZS output end Proof for theBenchmark
% 2.02/0.63  % (31486)------------------------------
% 2.02/0.63  % (31486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (31486)Termination reason: Refutation
% 2.02/0.63  
% 2.02/0.63  % (31486)Memory used [KB]: 11385
% 2.02/0.63  % (31486)Time elapsed: 0.202 s
% 2.02/0.63  % (31486)------------------------------
% 2.02/0.63  % (31486)------------------------------
% 2.02/0.63  % (31459)Success in time 0.27 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:34 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 483 expanded)
%              Number of leaves         :   25 ( 156 expanded)
%              Depth                    :   15
%              Number of atoms          :  371 (3373 expanded)
%              Number of equality atoms :   62 ( 102 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f187,f235,f257,f1093,f1103])).

fof(f1103,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f1102])).

fof(f1102,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1101,f160])).

fof(f160,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f77,f151])).

fof(f151,plain,(
    ! [X0] : k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f75,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f59,f58])).

fof(f58,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
          | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
        & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
        & r1_tarski(sK1,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        & v1_funct_2(X4,sK0,sK3)
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
        | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
      & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      & v1_funct_2(sK4,sK0,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f77,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f1101,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | spl8_3 ),
    inference(forward_demodulation,[],[f1098,f167])).

fof(f167,plain,(
    ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f156,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f156,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f84,f75,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1098,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f299,f166,f1096,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f1096,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl8_3 ),
    inference(forward_demodulation,[],[f142,f152])).

fof(f152,plain,(
    ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f73,f75,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f142,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f166,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f156,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f299,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f84,f159,f80])).

fof(f159,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(backward_demodulation,[],[f154,f152])).

fof(f154,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(unit_resulting_resolution,[],[f73,f75,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1093,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f1092])).

fof(f1092,plain,
    ( $false
    | spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f1091,f188])).

fof(f188,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl8_2 ),
    inference(forward_demodulation,[],[f138,f152])).

fof(f138,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1091,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f1088,f774])).

fof(f774,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f76,f336])).

fof(f336,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK0)
        | k1_relat_1(k7_relat_1(sK4,X4)) = X4 )
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f330,f156])).

fof(f330,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK0)
        | k1_relat_1(k7_relat_1(sK4,X4)) = X4
        | ~ v1_relat_1(sK4) )
    | ~ spl8_7 ),
    inference(superposition,[],[f87,f231])).

fof(f231,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl8_7
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f76,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f1088,plain,(
    v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f160,f484])).

fof(f484,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k9_relat_1(sK4,X4),X5)
      | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),X5) ) ),
    inference(subsumption_resolution,[],[f483,f299])).

fof(f483,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k9_relat_1(sK4,X4),X5)
      | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),X5)
      | ~ v1_relat_1(k7_relat_1(sK4,X4)) ) ),
    inference(subsumption_resolution,[],[f477,f158])).

fof(f158,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(backward_demodulation,[],[f153,f152])).

fof(f153,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f73,f75,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f477,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k9_relat_1(sK4,X4),X5)
      | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),X5)
      | ~ v1_funct_1(k7_relat_1(sK4,X4))
      | ~ v1_relat_1(k7_relat_1(sK4,X4)) ) ),
    inference(superposition,[],[f96,f167])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f257,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f251,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f251,plain,
    ( ! [X0,X1] : ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK5(X1)))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f218,f227])).

fof(f227,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f218,plain,(
    ! [X0,X1] : ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK5(X1))) ),
    inference(unit_resulting_resolution,[],[f145,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f145,plain,(
    ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK5(X1)))) ),
    inference(unit_resulting_resolution,[],[f83,f72,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f72,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f83,plain,(
    ! [X0] : v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(X0))
      & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f4,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f235,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f234,f229,f225])).

fof(f234,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f233,f75])).

fof(f233,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(subsumption_resolution,[],[f220,f74])).

fof(f74,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f220,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_funct_2(sK4,sK0,sK3)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(superposition,[],[f111,f148])).

fof(f148,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK0,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f75,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f187,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f157,f158])).

fof(f157,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl8_1 ),
    inference(backward_demodulation,[],[f134,f152])).

fof(f134,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f143,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f78,f140,f136,f132])).

fof(f78,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (16229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (16236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (16252)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (16231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (16245)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (16233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (16237)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (16241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (16253)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (16234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16240)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (16243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (16257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (16235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (16249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (16239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (16254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (16242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (16232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (16258)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (16251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (16255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (16246)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (16247)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (16250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (16238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (16256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (16248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.57  % (16251)Refutation not found, incomplete strategy% (16251)------------------------------
% 1.52/0.57  % (16251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (16251)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (16251)Memory used [KB]: 11001
% 1.52/0.57  % (16251)Time elapsed: 0.132 s
% 1.52/0.57  % (16251)------------------------------
% 1.52/0.57  % (16251)------------------------------
% 1.75/0.62  % (16255)Refutation found. Thanks to Tanya!
% 1.75/0.62  % SZS status Theorem for theBenchmark
% 1.75/0.62  % SZS output start Proof for theBenchmark
% 1.75/0.62  fof(f1104,plain,(
% 1.75/0.62    $false),
% 1.75/0.62    inference(avatar_sat_refutation,[],[f143,f187,f235,f257,f1093,f1103])).
% 1.75/0.62  fof(f1103,plain,(
% 1.75/0.62    spl8_3),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f1102])).
% 1.75/0.62  fof(f1102,plain,(
% 1.75/0.62    $false | spl8_3),
% 1.75/0.62    inference(subsumption_resolution,[],[f1101,f160])).
% 1.75/0.62  fof(f160,plain,(
% 1.75/0.62    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.75/0.62    inference(backward_demodulation,[],[f77,f151])).
% 1.75/0.62  fof(f151,plain,(
% 1.75/0.62    ( ! [X0] : (k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f75,f118])).
% 1.75/0.62  fof(f118,plain,(
% 1.75/0.62    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f53])).
% 1.75/0.62  fof(f53,plain,(
% 1.75/0.62    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.62    inference(ennf_transformation,[],[f19])).
% 1.75/0.62  fof(f19,axiom,(
% 1.75/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.75/0.62  fof(f75,plain,(
% 1.75/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  fof(f60,plain,(
% 1.75/0.62    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 1.75/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f59,f58])).
% 1.75/0.62  fof(f58,plain,(
% 1.75/0.62    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 1.75/0.62    introduced(choice_axiom,[])).
% 1.75/0.62  fof(f59,plain,(
% 1.75/0.62    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 1.75/0.62    introduced(choice_axiom,[])).
% 1.75/0.62  fof(f29,plain,(
% 1.75/0.62    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.75/0.62    inference(flattening,[],[f28])).
% 1.75/0.62  fof(f28,plain,(
% 1.75/0.62    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.75/0.62    inference(ennf_transformation,[],[f27])).
% 1.75/0.62  fof(f27,negated_conjecture,(
% 1.75/0.62    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.75/0.62    inference(negated_conjecture,[],[f26])).
% 1.75/0.62  fof(f26,conjecture,(
% 1.75/0.62    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 1.75/0.62  fof(f77,plain,(
% 1.75/0.62    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  fof(f1101,plain,(
% 1.75/0.62    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | spl8_3),
% 1.75/0.62    inference(forward_demodulation,[],[f1098,f167])).
% 1.75/0.62  fof(f167,plain,(
% 1.75/0.62    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f156,f86])).
% 1.75/0.62  fof(f86,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f33])).
% 1.75/0.62  fof(f33,plain,(
% 1.75/0.62    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.75/0.62    inference(ennf_transformation,[],[f11])).
% 1.75/0.62  fof(f11,axiom,(
% 1.75/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.75/0.62  fof(f156,plain,(
% 1.75/0.62    v1_relat_1(sK4)),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f84,f75,f80])).
% 1.75/0.62  fof(f80,plain,(
% 1.75/0.62    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f30])).
% 1.75/0.62  fof(f30,plain,(
% 1.75/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.75/0.62    inference(ennf_transformation,[],[f8])).
% 1.75/0.62  fof(f8,axiom,(
% 1.75/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.75/0.62  fof(f84,plain,(
% 1.75/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f10])).
% 1.75/0.62  fof(f10,axiom,(
% 1.75/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.75/0.62  fof(f1098,plain,(
% 1.75/0.62    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl8_3),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f299,f166,f1096,f107])).
% 1.75/0.62  fof(f107,plain,(
% 1.75/0.62    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f47])).
% 1.75/0.62  fof(f47,plain,(
% 1.75/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.75/0.62    inference(flattening,[],[f46])).
% 1.75/0.62  fof(f46,plain,(
% 1.75/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.75/0.62    inference(ennf_transformation,[],[f20])).
% 1.75/0.62  fof(f20,axiom,(
% 1.75/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.75/0.62  fof(f1096,plain,(
% 1.75/0.62    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl8_3),
% 1.75/0.62    inference(forward_demodulation,[],[f142,f152])).
% 1.75/0.62  fof(f152,plain,(
% 1.75/0.62    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f73,f75,f119])).
% 1.75/0.62  fof(f119,plain,(
% 1.75/0.62    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f55])).
% 1.75/0.62  fof(f55,plain,(
% 1.75/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.62    inference(flattening,[],[f54])).
% 1.75/0.62  fof(f54,plain,(
% 1.75/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.62    inference(ennf_transformation,[],[f24])).
% 1.75/0.62  fof(f24,axiom,(
% 1.75/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.75/0.62  fof(f73,plain,(
% 1.75/0.62    v1_funct_1(sK4)),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  fof(f142,plain,(
% 1.75/0.62    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl8_3),
% 1.75/0.62    inference(avatar_component_clause,[],[f140])).
% 1.75/0.62  fof(f140,plain,(
% 1.75/0.62    spl8_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.75/0.62  fof(f166,plain,(
% 1.75/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f156,f85])).
% 1.75/0.62  fof(f85,plain,(
% 1.75/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f32])).
% 1.75/0.62  fof(f32,plain,(
% 1.75/0.62    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.75/0.62    inference(ennf_transformation,[],[f13])).
% 1.75/0.62  fof(f13,axiom,(
% 1.75/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.75/0.62  fof(f299,plain,(
% 1.75/0.62    ( ! [X0] : (v1_relat_1(k7_relat_1(sK4,X0))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f84,f159,f80])).
% 1.75/0.62  fof(f159,plain,(
% 1.75/0.62    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 1.75/0.62    inference(backward_demodulation,[],[f154,f152])).
% 1.75/0.62  fof(f154,plain,(
% 1.75/0.62    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f73,f75,f121])).
% 1.75/0.62  fof(f121,plain,(
% 1.75/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f57])).
% 1.75/0.62  fof(f57,plain,(
% 1.75/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.62    inference(flattening,[],[f56])).
% 1.75/0.62  fof(f56,plain,(
% 1.75/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.62    inference(ennf_transformation,[],[f23])).
% 1.75/0.62  fof(f23,axiom,(
% 1.75/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.75/0.62  fof(f1093,plain,(
% 1.75/0.62    spl8_2 | ~spl8_7),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f1092])).
% 1.75/0.62  fof(f1092,plain,(
% 1.75/0.62    $false | (spl8_2 | ~spl8_7)),
% 1.75/0.62    inference(subsumption_resolution,[],[f1091,f188])).
% 1.75/0.62  fof(f188,plain,(
% 1.75/0.62    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl8_2),
% 1.75/0.62    inference(forward_demodulation,[],[f138,f152])).
% 1.75/0.62  fof(f138,plain,(
% 1.75/0.62    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl8_2),
% 1.75/0.62    inference(avatar_component_clause,[],[f136])).
% 1.75/0.62  fof(f136,plain,(
% 1.75/0.62    spl8_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.75/0.62  fof(f1091,plain,(
% 1.75/0.62    v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl8_7),
% 1.75/0.62    inference(forward_demodulation,[],[f1088,f774])).
% 1.75/0.62  fof(f774,plain,(
% 1.75/0.62    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl8_7),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f76,f336])).
% 1.75/0.62  fof(f336,plain,(
% 1.75/0.62    ( ! [X4] : (~r1_tarski(X4,sK0) | k1_relat_1(k7_relat_1(sK4,X4)) = X4) ) | ~spl8_7),
% 1.75/0.62    inference(subsumption_resolution,[],[f330,f156])).
% 1.75/0.62  fof(f330,plain,(
% 1.75/0.62    ( ! [X4] : (~r1_tarski(X4,sK0) | k1_relat_1(k7_relat_1(sK4,X4)) = X4 | ~v1_relat_1(sK4)) ) | ~spl8_7),
% 1.75/0.62    inference(superposition,[],[f87,f231])).
% 1.75/0.62  fof(f231,plain,(
% 1.75/0.62    sK0 = k1_relat_1(sK4) | ~spl8_7),
% 1.75/0.62    inference(avatar_component_clause,[],[f229])).
% 1.75/0.62  fof(f229,plain,(
% 1.75/0.62    spl8_7 <=> sK0 = k1_relat_1(sK4)),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.75/0.62  fof(f87,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f35])).
% 1.75/0.62  fof(f35,plain,(
% 1.75/0.62    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.75/0.62    inference(flattening,[],[f34])).
% 1.75/0.62  fof(f34,plain,(
% 1.75/0.62    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.75/0.62    inference(ennf_transformation,[],[f14])).
% 1.75/0.62  fof(f14,axiom,(
% 1.75/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.75/0.62  fof(f76,plain,(
% 1.75/0.62    r1_tarski(sK1,sK0)),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  fof(f1088,plain,(
% 1.75/0.62    v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),sK2)),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f160,f484])).
% 1.75/0.62  fof(f484,plain,(
% 1.75/0.62    ( ! [X4,X5] : (~r1_tarski(k9_relat_1(sK4,X4),X5) | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),X5)) )),
% 1.75/0.62    inference(subsumption_resolution,[],[f483,f299])).
% 1.75/0.62  fof(f483,plain,(
% 1.75/0.62    ( ! [X4,X5] : (~r1_tarski(k9_relat_1(sK4,X4),X5) | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),X5) | ~v1_relat_1(k7_relat_1(sK4,X4))) )),
% 1.75/0.62    inference(subsumption_resolution,[],[f477,f158])).
% 1.75/0.62  fof(f158,plain,(
% 1.75/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.75/0.62    inference(backward_demodulation,[],[f153,f152])).
% 1.75/0.62  fof(f153,plain,(
% 1.75/0.62    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f73,f75,f120])).
% 1.75/0.62  fof(f120,plain,(
% 1.75/0.62    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f57])).
% 1.75/0.62  fof(f477,plain,(
% 1.75/0.62    ( ! [X4,X5] : (~r1_tarski(k9_relat_1(sK4,X4),X5) | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),X5) | ~v1_funct_1(k7_relat_1(sK4,X4)) | ~v1_relat_1(k7_relat_1(sK4,X4))) )),
% 1.75/0.62    inference(superposition,[],[f96,f167])).
% 1.75/0.62  fof(f96,plain,(
% 1.75/0.62    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f42])).
% 1.75/0.62  fof(f42,plain,(
% 1.75/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.75/0.62    inference(flattening,[],[f41])).
% 1.75/0.62  fof(f41,plain,(
% 1.75/0.62    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.75/0.62    inference(ennf_transformation,[],[f25])).
% 1.75/0.62  fof(f25,axiom,(
% 1.75/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.75/0.62  fof(f257,plain,(
% 1.75/0.62    ~spl8_6),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f256])).
% 1.75/0.62  fof(f256,plain,(
% 1.75/0.62    $false | ~spl8_6),
% 1.75/0.62    inference(subsumption_resolution,[],[f251,f79])).
% 1.75/0.62  fof(f79,plain,(
% 1.75/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f3])).
% 1.75/0.62  fof(f3,axiom,(
% 1.75/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.75/0.62  fof(f251,plain,(
% 1.75/0.62    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK5(X1)))) ) | ~spl8_6),
% 1.75/0.62    inference(backward_demodulation,[],[f218,f227])).
% 1.75/0.62  fof(f227,plain,(
% 1.75/0.62    k1_xboole_0 = sK3 | ~spl8_6),
% 1.75/0.62    inference(avatar_component_clause,[],[f225])).
% 1.75/0.62  fof(f225,plain,(
% 1.75/0.62    spl8_6 <=> k1_xboole_0 = sK3),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.75/0.62  fof(f218,plain,(
% 1.75/0.62    ( ! [X0,X1] : (~r1_tarski(sK3,k2_zfmisc_1(X0,sK5(X1)))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f145,f106])).
% 1.75/0.62  fof(f106,plain,(
% 1.75/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f70])).
% 1.75/0.62  fof(f70,plain,(
% 1.75/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.75/0.62    inference(nnf_transformation,[],[f6])).
% 1.75/0.62  fof(f6,axiom,(
% 1.75/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.75/0.62  fof(f145,plain,(
% 1.75/0.62    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK5(X1))))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f83,f72,f90])).
% 1.75/0.62  fof(f90,plain,(
% 1.75/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f37])).
% 1.75/0.62  fof(f37,plain,(
% 1.75/0.62    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.75/0.62    inference(ennf_transformation,[],[f17])).
% 1.75/0.62  fof(f17,axiom,(
% 1.75/0.62    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.75/0.62  fof(f72,plain,(
% 1.75/0.62    ~v1_xboole_0(sK3)),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  fof(f83,plain,(
% 1.75/0.62    ( ! [X0] : (v1_xboole_0(sK5(X0))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f62])).
% 1.75/0.62  fof(f62,plain,(
% 1.75/0.62    ! [X0] : (v1_xboole_0(sK5(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)))),
% 1.75/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f4,f61])).
% 1.75/0.62  fof(f61,plain,(
% 1.75/0.62    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK5(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(X0))))),
% 1.75/0.62    introduced(choice_axiom,[])).
% 1.75/0.62  fof(f4,axiom,(
% 1.75/0.62    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.75/0.62  fof(f235,plain,(
% 1.75/0.62    spl8_6 | spl8_7),
% 1.75/0.62    inference(avatar_split_clause,[],[f234,f229,f225])).
% 1.75/0.62  fof(f234,plain,(
% 1.75/0.62    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 1.75/0.62    inference(subsumption_resolution,[],[f233,f75])).
% 1.75/0.62  fof(f233,plain,(
% 1.75/0.62    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.75/0.62    inference(subsumption_resolution,[],[f220,f74])).
% 1.75/0.62  fof(f74,plain,(
% 1.75/0.62    v1_funct_2(sK4,sK0,sK3)),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  fof(f220,plain,(
% 1.75/0.62    sK0 = k1_relat_1(sK4) | ~v1_funct_2(sK4,sK0,sK3) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.75/0.62    inference(superposition,[],[f111,f148])).
% 1.75/0.62  fof(f148,plain,(
% 1.75/0.62    k1_relat_1(sK4) = k1_relset_1(sK0,sK3,sK4)),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f75,f108])).
% 1.75/0.62  fof(f108,plain,(
% 1.75/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f48])).
% 1.75/0.62  fof(f48,plain,(
% 1.75/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.62    inference(ennf_transformation,[],[f18])).
% 1.75/0.62  fof(f18,axiom,(
% 1.75/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.75/0.62  fof(f111,plain,(
% 1.75/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f71])).
% 1.75/0.62  fof(f71,plain,(
% 1.75/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.62    inference(nnf_transformation,[],[f51])).
% 1.75/0.62  fof(f51,plain,(
% 1.75/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.62    inference(flattening,[],[f50])).
% 1.75/0.62  fof(f50,plain,(
% 1.75/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.62    inference(ennf_transformation,[],[f22])).
% 1.75/0.62  fof(f22,axiom,(
% 1.75/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.75/0.62  fof(f187,plain,(
% 1.75/0.62    spl8_1),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f185])).
% 1.75/0.62  fof(f185,plain,(
% 1.75/0.62    $false | spl8_1),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f157,f158])).
% 1.75/0.62  fof(f157,plain,(
% 1.75/0.62    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl8_1),
% 1.75/0.62    inference(backward_demodulation,[],[f134,f152])).
% 1.75/0.62  fof(f134,plain,(
% 1.75/0.62    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl8_1),
% 1.75/0.62    inference(avatar_component_clause,[],[f132])).
% 1.75/0.62  fof(f132,plain,(
% 1.75/0.62    spl8_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.75/0.62  fof(f143,plain,(
% 1.75/0.62    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.75/0.62    inference(avatar_split_clause,[],[f78,f140,f136,f132])).
% 1.75/0.62  fof(f78,plain,(
% 1.75/0.62    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.75/0.62    inference(cnf_transformation,[],[f60])).
% 1.75/0.62  % SZS output end Proof for theBenchmark
% 1.75/0.62  % (16255)------------------------------
% 1.75/0.62  % (16255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.62  % (16255)Termination reason: Refutation
% 1.75/0.62  
% 1.75/0.62  % (16255)Memory used [KB]: 11641
% 1.75/0.62  % (16255)Time elapsed: 0.223 s
% 1.75/0.62  % (16255)------------------------------
% 1.75/0.62  % (16255)------------------------------
% 1.75/0.63  % (16228)Success in time 0.269 s
%------------------------------------------------------------------------------

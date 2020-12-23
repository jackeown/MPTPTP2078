%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 438 expanded)
%              Number of leaves         :   25 ( 150 expanded)
%              Depth                    :   16
%              Number of atoms          :  534 (2603 expanded)
%              Number of equality atoms :  140 ( 507 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f429,f550,f601,f602,f674,f699,f706,f835,f1741,f1769])).

fof(f1769,plain,(
    ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f1768])).

fof(f1768,plain,
    ( $false
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1745,f238])).

fof(f238,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
              | ~ m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK3,sK4,sK5,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
            | ~ m1_subset_1(X4,sK3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
      & ! [X4] :
          ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
          | ~ m1_subset_1(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f1745,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f61,f403])).

fof(f403,plain,
    ( sK5 = sK6
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl9_12
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f61,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f1741,plain,
    ( spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f1740,f468,f458,f426,f401])).

fof(f426,plain,
    ( spl9_13
  <=> m1_subset_1(sK7(sK5,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f458,plain,
    ( spl9_14
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f468,plain,
    ( spl9_16
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f1740,plain,
    ( sK5 = sK6
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f1739,f1290])).

fof(f1290,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl9_16 ),
    inference(resolution,[],[f856,f124])).

fof(f124,plain,(
    v4_relat_1(sK6,sK3) ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f856,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(sK6,X1)
        | r1_tarski(sK3,X1) )
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f845,f102])).

fof(f102,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f76,f59])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f845,plain,
    ( ! [X1] :
        ( r1_tarski(sK3,X1)
        | ~ v4_relat_1(sK6,X1)
        | ~ v1_relat_1(sK6) )
    | ~ spl9_16 ),
    inference(superposition,[],[f67,f470])).

fof(f470,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f468])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1739,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK5 = sK6
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f1738,f460])).

fof(f460,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f458])).

fof(f1738,plain,
    ( sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f1737,f470])).

fof(f1737,plain,
    ( sK3 != k1_relat_1(sK6)
    | sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f1736,f460])).

fof(f1736,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13 ),
    inference(subsumption_resolution,[],[f1735,f101])).

fof(f101,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f76,f56])).

fof(f1735,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13 ),
    inference(subsumption_resolution,[],[f1734,f54])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f1734,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13 ),
    inference(subsumption_resolution,[],[f1733,f102])).

fof(f1733,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13 ),
    inference(subsumption_resolution,[],[f1723,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f1723,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl9_13 ),
    inference(resolution,[],[f341,f428])).

fof(f428,plain,
    ( ~ m1_subset_1(sK7(sK5,sK6),sK3)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f426])).

fof(f341,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1),X2)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1
      | ~ r1_tarski(k1_relat_1(X0),X2) ) ),
    inference(resolution,[],[f64,f209])).

fof(f209,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X4)
      | m1_subset_1(X2,X3)
      | ~ r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f88,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f835,plain,
    ( ~ spl9_25
    | ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f834])).

fof(f834,plain,
    ( $false
    | ~ spl9_25
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f762,f751])).

fof(f751,plain,
    ( r2_relset_1(sK3,sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f239,f698])).

fof(f698,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f696])).

fof(f696,plain,
    ( spl9_27
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f239,plain,(
    r2_relset_1(sK3,sK4,sK6,sK6) ),
    inference(resolution,[],[f96,f59])).

fof(f762,plain,
    ( ~ r2_relset_1(sK3,sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl9_25
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f761,f669])).

fof(f669,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl9_25
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f761,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,k1_xboole_0)
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f61,f698])).

fof(f706,plain,
    ( ~ spl9_15
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | ~ spl9_15
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f701,f95])).

fof(f95,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f701,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_15
    | ~ spl9_26 ),
    inference(backward_demodulation,[],[f492,f673])).

fof(f673,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl9_26
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f492,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f464,f473])).

fof(f473,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_15 ),
    inference(resolution,[],[f464,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f464,plain,
    ( sP0(sK3,sK4)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl9_15
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f699,plain,
    ( spl9_27
    | spl9_26
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f694,f462,f671,f696])).

fof(f694,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f693,f611])).

fof(f611,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f58,f473])).

fof(f58,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f693,plain,
    ( ~ v1_funct_2(sK6,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ spl9_15 ),
    inference(resolution,[],[f622,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f622,plain,
    ( sP2(sK6,k1_xboole_0,sK3)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f198,f473])).

fof(f198,plain,(
    sP2(sK6,sK4,sK3) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f674,plain,
    ( spl9_25
    | spl9_26
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f665,f462,f671,f667])).

fof(f665,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f664,f609])).

fof(f609,plain,
    ( v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f55,f473])).

fof(f55,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f664,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl9_15 ),
    inference(resolution,[],[f621,f94])).

fof(f621,plain,
    ( sP2(sK5,k1_xboole_0,sK3)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f197,f473])).

fof(f197,plain,(
    sP2(sK5,sK4,sK3) ),
    inference(resolution,[],[f87,f56])).

fof(f602,plain,
    ( spl9_14
    | spl9_15 ),
    inference(avatar_split_clause,[],[f511,f462,f458])).

fof(f511,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f508,f55])).

fof(f508,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f56,f313])).

fof(f313,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f311,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f311,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f82,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f601,plain,
    ( spl9_16
    | spl9_15 ),
    inference(avatar_split_clause,[],[f536,f462,f468])).

fof(f536,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f533,f58])).

fof(f533,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(resolution,[],[f59,f313])).

fof(f550,plain,
    ( ~ spl9_16
    | spl9_11
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f539,f458,f397,f468])).

fof(f397,plain,
    ( spl9_11
  <=> k1_relat_1(sK6) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f539,plain,
    ( sK3 != k1_relat_1(sK6)
    | spl9_11
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f399,f460])).

fof(f399,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f397])).

fof(f429,plain,
    ( ~ spl9_13
    | ~ spl9_11
    | spl9_12 ),
    inference(avatar_split_clause,[],[f424,f401,f397,f426])).

fof(f424,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(subsumption_resolution,[],[f423,f101])).

fof(f423,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(subsumption_resolution,[],[f422,f54])).

fof(f422,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(equality_resolution,[],[f379])).

fof(f379,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(subsumption_resolution,[],[f378,f102])).

fof(f378,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(subsumption_resolution,[],[f373,f57])).

fof(f373,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(superposition,[],[f65,f60])).

fof(f60,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (26365)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (26365)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (26375)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (26383)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1775,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f429,f550,f601,f602,f674,f699,f706,f835,f1741,f1769])).
% 0.21/0.51  fof(f1769,plain,(
% 0.21/0.51    ~spl9_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1768])).
% 0.21/0.51  fof(f1768,plain,(
% 0.21/0.51    $false | ~spl9_12),
% 0.21/0.51    inference(subsumption_resolution,[],[f1745,f238])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    r2_relset_1(sK3,sK4,sK5,sK5)),
% 0.21/0.51    inference(resolution,[],[f96,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f39,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.51    inference(condensation,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.51  fof(f1745,plain,(
% 0.21/0.51    ~r2_relset_1(sK3,sK4,sK5,sK5) | ~spl9_12),
% 0.21/0.51    inference(backward_demodulation,[],[f61,f403])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    sK5 = sK6 | ~spl9_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f401])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    spl9_12 <=> sK5 = sK6),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f1741,plain,(
% 0.21/0.51    spl9_12 | spl9_13 | ~spl9_14 | ~spl9_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f1740,f468,f458,f426,f401])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    spl9_13 <=> m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    spl9_14 <=> sK3 = k1_relat_1(sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.51  fof(f468,plain,(
% 0.21/0.51    spl9_16 <=> sK3 = k1_relat_1(sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.51  fof(f1740,plain,(
% 0.21/0.51    sK5 = sK6 | (spl9_13 | ~spl9_14 | ~spl9_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1739,f1290])).
% 0.21/0.51  fof(f1290,plain,(
% 0.21/0.51    r1_tarski(sK3,sK3) | ~spl9_16),
% 0.21/0.51    inference(resolution,[],[f856,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    v4_relat_1(sK6,sK3)),
% 0.21/0.51    inference(resolution,[],[f78,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f856,plain,(
% 0.21/0.51    ( ! [X1] : (~v4_relat_1(sK6,X1) | r1_tarski(sK3,X1)) ) | ~spl9_16),
% 0.21/0.51    inference(subsumption_resolution,[],[f845,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    v1_relat_1(sK6)),
% 0.21/0.51    inference(resolution,[],[f76,f59])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f845,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(sK3,X1) | ~v4_relat_1(sK6,X1) | ~v1_relat_1(sK6)) ) | ~spl9_16),
% 0.21/0.51    inference(superposition,[],[f67,f470])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    sK3 = k1_relat_1(sK6) | ~spl9_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f468])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.51  fof(f1739,plain,(
% 0.21/0.51    ~r1_tarski(sK3,sK3) | sK5 = sK6 | (spl9_13 | ~spl9_14 | ~spl9_16)),
% 0.21/0.51    inference(forward_demodulation,[],[f1738,f460])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    sK3 = k1_relat_1(sK5) | ~spl9_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f458])).
% 0.21/0.51  fof(f1738,plain,(
% 0.21/0.51    sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | (spl9_13 | ~spl9_14 | ~spl9_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1737,f470])).
% 0.21/0.51  fof(f1737,plain,(
% 0.21/0.51    sK3 != k1_relat_1(sK6) | sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | (spl9_13 | ~spl9_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f1736,f460])).
% 0.21/0.51  fof(f1736,plain,(
% 0.21/0.51    k1_relat_1(sK6) != k1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | spl9_13),
% 0.21/0.51    inference(subsumption_resolution,[],[f1735,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    v1_relat_1(sK5)),
% 0.21/0.51    inference(resolution,[],[f76,f56])).
% 0.21/0.51  fof(f1735,plain,(
% 0.21/0.51    k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | spl9_13),
% 0.21/0.51    inference(subsumption_resolution,[],[f1734,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    v1_funct_1(sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f1734,plain,(
% 0.21/0.51    k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | spl9_13),
% 0.21/0.51    inference(subsumption_resolution,[],[f1733,f102])).
% 0.21/0.51  fof(f1733,plain,(
% 0.21/0.51    k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | spl9_13),
% 0.21/0.51    inference(subsumption_resolution,[],[f1723,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_funct_1(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f1723,plain,(
% 0.21/0.51    k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(k1_relat_1(sK5),sK3) | spl9_13),
% 0.21/0.51    inference(resolution,[],[f341,f428])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    ~m1_subset_1(sK7(sK5,sK6),sK3) | spl9_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f426])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1),X2) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | X0 = X1 | ~r1_tarski(k1_relat_1(X0),X2)) )),
% 0.21/0.51    inference(resolution,[],[f64,f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~r2_hidden(X2,X4) | m1_subset_1(X2,X3) | ~r1_tarski(X4,X3)) )),
% 0.21/0.51    inference(resolution,[],[f88,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.51  fof(f835,plain,(
% 0.21/0.51    ~spl9_25 | ~spl9_27),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f834])).
% 0.21/0.51  fof(f834,plain,(
% 0.21/0.51    $false | (~spl9_25 | ~spl9_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f762,f751])).
% 0.21/0.51  fof(f751,plain,(
% 0.21/0.51    r2_relset_1(sK3,sK4,k1_xboole_0,k1_xboole_0) | ~spl9_27),
% 0.21/0.51    inference(forward_demodulation,[],[f239,f698])).
% 0.21/0.51  fof(f698,plain,(
% 0.21/0.51    k1_xboole_0 = sK6 | ~spl9_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f696])).
% 0.21/0.51  fof(f696,plain,(
% 0.21/0.51    spl9_27 <=> k1_xboole_0 = sK6),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    r2_relset_1(sK3,sK4,sK6,sK6)),
% 0.21/0.51    inference(resolution,[],[f96,f59])).
% 0.21/0.51  fof(f762,plain,(
% 0.21/0.51    ~r2_relset_1(sK3,sK4,k1_xboole_0,k1_xboole_0) | (~spl9_25 | ~spl9_27)),
% 0.21/0.51    inference(forward_demodulation,[],[f761,f669])).
% 0.21/0.51  fof(f669,plain,(
% 0.21/0.51    k1_xboole_0 = sK5 | ~spl9_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f667])).
% 0.21/0.51  fof(f667,plain,(
% 0.21/0.51    spl9_25 <=> k1_xboole_0 = sK5),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    ~r2_relset_1(sK3,sK4,sK5,k1_xboole_0) | ~spl9_27),
% 0.21/0.51    inference(forward_demodulation,[],[f61,f698])).
% 0.21/0.51  fof(f706,plain,(
% 0.21/0.51    ~spl9_15 | ~spl9_26),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f705])).
% 0.21/0.51  fof(f705,plain,(
% 0.21/0.51    $false | (~spl9_15 | ~spl9_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f701,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f701,plain,(
% 0.21/0.51    sP0(k1_xboole_0,k1_xboole_0) | (~spl9_15 | ~spl9_26)),
% 0.21/0.51    inference(backward_demodulation,[],[f492,f673])).
% 0.21/0.51  fof(f673,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | ~spl9_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f671])).
% 0.21/0.51  fof(f671,plain,(
% 0.21/0.51    spl9_26 <=> k1_xboole_0 = sK3),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    sP0(sK3,k1_xboole_0) | ~spl9_15),
% 0.21/0.51    inference(backward_demodulation,[],[f464,f473])).
% 0.21/0.51  fof(f473,plain,(
% 0.21/0.51    k1_xboole_0 = sK4 | ~spl9_15),
% 0.21/0.51    inference(resolution,[],[f464,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    sP0(sK3,sK4) | ~spl9_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f462])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    spl9_15 <=> sP0(sK3,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.51  fof(f699,plain,(
% 0.21/0.51    spl9_27 | spl9_26 | ~spl9_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f694,f462,f671,f696])).
% 0.21/0.51  fof(f694,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~spl9_15),
% 0.21/0.51    inference(subsumption_resolution,[],[f693,f611])).
% 0.21/0.51  fof(f611,plain,(
% 0.21/0.51    v1_funct_2(sK6,sK3,k1_xboole_0) | ~spl9_15),
% 0.21/0.51    inference(backward_demodulation,[],[f58,f473])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f693,plain,(
% 0.21/0.51    ~v1_funct_2(sK6,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~spl9_15),
% 0.21/0.51    inference(resolution,[],[f622,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(equality_resolution,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f622,plain,(
% 0.21/0.51    sP2(sK6,k1_xboole_0,sK3) | ~spl9_15),
% 0.21/0.51    inference(backward_demodulation,[],[f198,f473])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    sP2(sK6,sK4,sK3)),
% 0.21/0.51    inference(resolution,[],[f87,f59])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(definition_folding,[],[f29,f36,f35,f34])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f674,plain,(
% 0.21/0.51    spl9_25 | spl9_26 | ~spl9_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f665,f462,f671,f667])).
% 0.21/0.51  fof(f665,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl9_15),
% 0.21/0.51    inference(subsumption_resolution,[],[f664,f609])).
% 0.21/0.51  fof(f609,plain,(
% 0.21/0.51    v1_funct_2(sK5,sK3,k1_xboole_0) | ~spl9_15),
% 0.21/0.51    inference(backward_demodulation,[],[f55,f473])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_funct_2(sK5,sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f664,plain,(
% 0.21/0.51    ~v1_funct_2(sK5,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl9_15),
% 0.21/0.51    inference(resolution,[],[f621,f94])).
% 0.21/0.51  fof(f621,plain,(
% 0.21/0.51    sP2(sK5,k1_xboole_0,sK3) | ~spl9_15),
% 0.21/0.51    inference(backward_demodulation,[],[f197,f473])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    sP2(sK5,sK4,sK3)),
% 0.21/0.51    inference(resolution,[],[f87,f56])).
% 0.21/0.51  fof(f602,plain,(
% 0.21/0.51    spl9_14 | spl9_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f511,f462,f458])).
% 0.21/0.51  fof(f511,plain,(
% 0.21/0.51    sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f508,f55])).
% 0.21/0.51  fof(f508,plain,(
% 0.21/0.51    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.21/0.51    inference(resolution,[],[f56,f313])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f311,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.51    inference(superposition,[],[f82,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f35])).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    spl9_16 | spl9_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f536,f462,f468])).
% 0.21/0.51  fof(f536,plain,(
% 0.21/0.51    sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f533,f58])).
% 0.21/0.51  fof(f533,plain,(
% 0.21/0.51    ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.21/0.51    inference(resolution,[],[f59,f313])).
% 0.21/0.51  fof(f550,plain,(
% 0.21/0.51    ~spl9_16 | spl9_11 | ~spl9_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f539,f458,f397,f468])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    spl9_11 <=> k1_relat_1(sK6) = k1_relat_1(sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.51  fof(f539,plain,(
% 0.21/0.51    sK3 != k1_relat_1(sK6) | (spl9_11 | ~spl9_14)),
% 0.21/0.51    inference(backward_demodulation,[],[f399,f460])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    k1_relat_1(sK6) != k1_relat_1(sK5) | spl9_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f397])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    ~spl9_13 | ~spl9_11 | spl9_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f424,f401,f397,f426])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f423,f101])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f422,f54])).
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.51    inference(equality_resolution,[],[f379])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f378,f102])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f373,f57])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 0.21/0.51    inference(superposition,[],[f65,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26365)------------------------------
% 0.21/0.51  % (26365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26365)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26365)Memory used [KB]: 6780
% 0.21/0.51  % (26365)Time elapsed: 0.054 s
% 0.21/0.51  % (26365)------------------------------
% 0.21/0.51  % (26365)------------------------------
% 0.21/0.51  % (26360)Success in time 0.151 s
%------------------------------------------------------------------------------

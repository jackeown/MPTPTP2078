%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:22 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 202 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  220 (1054 expanded)
%              Number of equality atoms :   27 ( 155 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f667,plain,(
    $false ),
    inference(subsumption_resolution,[],[f666,f657])).

fof(f657,plain,(
    r2_hidden(sK10(sK4,sK2,sK3),sK0) ),
    inference(resolution,[],[f309,f254])).

fof(f254,plain,(
    r2_hidden(k4_tarski(sK10(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f249,f201])).

fof(f201,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f111,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f111,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f48,f82,f81])).

fof(f81,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f39])).

fof(f39,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f38,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f249,plain,
    ( r2_hidden(k4_tarski(sK10(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f221,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
            & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f103,f104])).

fof(f104,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
        & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f221,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f112,f204])).

fof(f204,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f111,f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f112,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f83])).

fof(f309,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
      | r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f209,f173])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f209,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,sK3) ) ),
    inference(resolution,[],[f111,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f666,plain,(
    ~ r2_hidden(sK10(sK4,sK2,sK3),sK0) ),
    inference(resolution,[],[f665,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f665,plain,(
    ~ m1_subset_1(sK10(sK4,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f664,f255])).

fof(f255,plain,(
    r2_hidden(sK10(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f250,f201])).

fof(f250,plain,
    ( r2_hidden(sK10(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f221,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK10(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f664,plain,
    ( ~ r2_hidden(sK10(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK10(sK4,sK2,sK3),sK0) ),
    inference(trivial_inequality_removal,[],[f663])).

fof(f663,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK10(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK10(sK4,sK2,sK3),sK0) ),
    inference(superposition,[],[f113,f330])).

fof(f330,plain,(
    sK4 = k1_funct_1(sK3,sK10(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f329,f201])).

fof(f329,plain,
    ( sK4 = k1_funct_1(sK3,sK10(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f325,f110])).

fof(f110,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f325,plain,
    ( sK4 = k1_funct_1(sK3,sK10(sK4,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f254,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f113,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (25870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (25862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (25853)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (25848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (25851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (25852)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (25847)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (25859)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (25850)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (25849)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (25856)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (25877)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (25871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (25876)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (25861)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (25864)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (25875)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (25863)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (25872)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (25866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (25858)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (25857)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (25854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (25869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (25857)Refutation not found, incomplete strategy% (25857)------------------------------
% 0.22/0.56  % (25857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (25857)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (25857)Memory used [KB]: 10746
% 0.22/0.56  % (25857)Time elapsed: 0.140 s
% 0.22/0.56  % (25857)------------------------------
% 0.22/0.56  % (25857)------------------------------
% 0.22/0.56  % (25878)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (25868)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (25874)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (25870)Refutation not found, incomplete strategy% (25870)------------------------------
% 0.22/0.56  % (25870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (25870)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (25870)Memory used [KB]: 11513
% 0.22/0.57  % (25870)Time elapsed: 0.116 s
% 0.22/0.57  % (25870)------------------------------
% 0.22/0.57  % (25870)------------------------------
% 0.22/0.57  % (25855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (25860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.57  % (25865)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.66/0.60  % (25855)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f667,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(subsumption_resolution,[],[f666,f657])).
% 1.66/0.60  fof(f657,plain,(
% 1.66/0.60    r2_hidden(sK10(sK4,sK2,sK3),sK0)),
% 1.66/0.60    inference(resolution,[],[f309,f254])).
% 1.66/0.60  fof(f254,plain,(
% 1.66/0.60    r2_hidden(k4_tarski(sK10(sK4,sK2,sK3),sK4),sK3)),
% 1.66/0.60    inference(subsumption_resolution,[],[f249,f201])).
% 1.66/0.60  fof(f201,plain,(
% 1.66/0.60    v1_relat_1(sK3)),
% 1.66/0.60    inference(resolution,[],[f111,f163])).
% 1.66/0.60  fof(f163,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f71])).
% 1.66/0.60  fof(f71,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.60    inference(ennf_transformation,[],[f26])).
% 1.66/0.60  fof(f26,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.66/0.60  fof(f111,plain,(
% 1.66/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.60    inference(cnf_transformation,[],[f83])).
% 1.66/0.60  fof(f83,plain,(
% 1.66/0.60    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f48,f82,f81])).
% 1.66/0.60  fof(f81,plain,(
% 1.66/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f82,plain,(
% 1.66/0.60    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f48,plain,(
% 1.66/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.66/0.60    inference(flattening,[],[f47])).
% 1.66/0.60  fof(f47,plain,(
% 1.66/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.66/0.60    inference(ennf_transformation,[],[f41])).
% 1.66/0.60  fof(f41,plain,(
% 1.66/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.66/0.60    inference(pure_predicate_removal,[],[f39])).
% 1.85/0.61  fof(f39,negated_conjecture,(
% 1.85/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.85/0.61    inference(negated_conjecture,[],[f38])).
% 1.85/0.61  fof(f38,conjecture,(
% 1.85/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 1.85/0.61  fof(f249,plain,(
% 1.85/0.61    r2_hidden(k4_tarski(sK10(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.85/0.61    inference(resolution,[],[f221,f160])).
% 1.85/0.61  fof(f160,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f105])).
% 1.85/0.61  fof(f105,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f103,f104])).
% 1.85/0.61  fof(f104,plain,(
% 1.85/0.61    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f103,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(rectify,[],[f102])).
% 1.85/0.61  fof(f102,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(nnf_transformation,[],[f70])).
% 1.85/0.61  fof(f70,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(ennf_transformation,[],[f17])).
% 1.85/0.61  fof(f17,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.85/0.61  fof(f221,plain,(
% 1.85/0.61    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.85/0.61    inference(backward_demodulation,[],[f112,f204])).
% 1.85/0.61  fof(f204,plain,(
% 1.85/0.61    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.85/0.61    inference(resolution,[],[f111,f172])).
% 1.85/0.61  fof(f172,plain,(
% 1.85/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f80])).
% 1.85/0.61  fof(f80,plain,(
% 1.85/0.61    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.61    inference(ennf_transformation,[],[f30])).
% 1.85/0.61  fof(f30,axiom,(
% 1.85/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.85/0.61  fof(f112,plain,(
% 1.85/0.61    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.85/0.61    inference(cnf_transformation,[],[f83])).
% 1.85/0.61  fof(f309,plain,(
% 1.85/0.61    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X2,sK0)) )),
% 1.85/0.61    inference(resolution,[],[f209,f173])).
% 1.85/0.61  fof(f173,plain,(
% 1.85/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f109])).
% 1.85/0.61  fof(f109,plain,(
% 1.85/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.85/0.61    inference(flattening,[],[f108])).
% 1.85/0.61  fof(f108,plain,(
% 1.85/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.85/0.61    inference(nnf_transformation,[],[f5])).
% 1.85/0.61  fof(f5,axiom,(
% 1.85/0.61    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 1.85/0.61  fof(f209,plain,(
% 1.85/0.61    ( ! [X5] : (r2_hidden(X5,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3)) )),
% 1.85/0.61    inference(resolution,[],[f111,f146])).
% 1.85/0.61  fof(f146,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f60])).
% 1.85/0.61  fof(f60,plain,(
% 1.85/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/0.61    inference(ennf_transformation,[],[f10])).
% 1.85/0.61  fof(f10,axiom,(
% 1.85/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.85/0.61  fof(f666,plain,(
% 1.85/0.61    ~r2_hidden(sK10(sK4,sK2,sK3),sK0)),
% 1.85/0.61    inference(resolution,[],[f665,f143])).
% 1.85/0.61  fof(f143,plain,(
% 1.85/0.61    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f58])).
% 1.85/0.61  fof(f58,plain,(
% 1.85/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f14])).
% 1.85/0.61  fof(f14,axiom,(
% 1.85/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.85/0.61  fof(f665,plain,(
% 1.85/0.61    ~m1_subset_1(sK10(sK4,sK2,sK3),sK0)),
% 1.85/0.61    inference(subsumption_resolution,[],[f664,f255])).
% 1.85/0.61  fof(f255,plain,(
% 1.85/0.61    r2_hidden(sK10(sK4,sK2,sK3),sK2)),
% 1.85/0.61    inference(subsumption_resolution,[],[f250,f201])).
% 1.85/0.61  fof(f250,plain,(
% 1.85/0.61    r2_hidden(sK10(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.85/0.61    inference(resolution,[],[f221,f161])).
% 1.85/0.61  fof(f161,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK10(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f105])).
% 1.85/0.61  fof(f664,plain,(
% 1.85/0.61    ~r2_hidden(sK10(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK10(sK4,sK2,sK3),sK0)),
% 1.85/0.61    inference(trivial_inequality_removal,[],[f663])).
% 1.85/0.61  fof(f663,plain,(
% 1.85/0.61    sK4 != sK4 | ~r2_hidden(sK10(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK10(sK4,sK2,sK3),sK0)),
% 1.85/0.61    inference(superposition,[],[f113,f330])).
% 1.85/0.61  fof(f330,plain,(
% 1.85/0.61    sK4 = k1_funct_1(sK3,sK10(sK4,sK2,sK3))),
% 1.85/0.61    inference(subsumption_resolution,[],[f329,f201])).
% 1.85/0.61  fof(f329,plain,(
% 1.85/0.61    sK4 = k1_funct_1(sK3,sK10(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.85/0.61    inference(subsumption_resolution,[],[f325,f110])).
% 1.85/0.61  fof(f110,plain,(
% 1.85/0.61    v1_funct_1(sK3)),
% 1.85/0.61    inference(cnf_transformation,[],[f83])).
% 1.85/0.61  fof(f325,plain,(
% 1.85/0.61    sK4 = k1_funct_1(sK3,sK10(sK4,sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.85/0.61    inference(resolution,[],[f254,f169])).
% 1.85/0.61  fof(f169,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f107])).
% 1.85/0.61  fof(f107,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(flattening,[],[f106])).
% 1.85/0.61  fof(f106,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(nnf_transformation,[],[f77])).
% 1.85/0.61  fof(f77,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(flattening,[],[f76])).
% 1.85/0.61  fof(f76,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.85/0.61    inference(ennf_transformation,[],[f24])).
% 1.85/0.61  fof(f24,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.85/0.61  fof(f113,plain,(
% 1.85/0.61    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f83])).
% 1.85/0.61  % SZS output end Proof for theBenchmark
% 1.85/0.61  % (25855)------------------------------
% 1.85/0.61  % (25855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (25855)Termination reason: Refutation
% 1.85/0.61  
% 1.85/0.61  % (25855)Memory used [KB]: 11001
% 1.85/0.61  % (25855)Time elapsed: 0.184 s
% 1.85/0.61  % (25855)------------------------------
% 1.85/0.61  % (25855)------------------------------
% 1.85/0.61  % (25840)Success in time 0.24 s
%------------------------------------------------------------------------------

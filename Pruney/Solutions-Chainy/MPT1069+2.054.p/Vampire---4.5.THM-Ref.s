%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:50 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 579 expanded)
%              Number of leaves         :   56 ( 242 expanded)
%              Depth                    :   14
%              Number of atoms          :  799 (3464 expanded)
%              Number of equality atoms :  126 ( 746 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f709,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f139,f155,f169,f173,f179,f292,f309,f357,f371,f381,f439,f441,f443,f445,f448,f454,f465,f488,f490,f503,f512,f529,f542,f549,f562,f580,f604,f645,f675,f708])).

fof(f708,plain,
    ( spl11_16
    | ~ spl11_28
    | ~ spl11_47 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | spl11_16
    | ~ spl11_28
    | ~ spl11_47 ),
    inference(resolution,[],[f688,f73])).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f688,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl11_16
    | ~ spl11_28
    | ~ spl11_47 ),
    inference(backward_demodulation,[],[f274,f683])).

fof(f683,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_28
    | ~ spl11_47 ),
    inference(backward_demodulation,[],[f560,f379])).

fof(f379,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl11_28
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f560,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl11_47
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f274,plain,
    ( ~ v1_xboole_0(sK2)
    | spl11_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl11_16
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f675,plain,
    ( ~ spl11_2
    | ~ spl11_20
    | ~ spl11_41 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_20
    | ~ spl11_41 ),
    inference(resolution,[],[f661,f73])).

fof(f661,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl11_2
    | ~ spl11_20
    | ~ spl11_41 ),
    inference(backward_demodulation,[],[f392,f632])).

fof(f632,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ spl11_2
    | ~ spl11_41 ),
    inference(resolution,[],[f628,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f628,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK4))
    | ~ spl11_2
    | ~ spl11_41 ),
    inference(resolution,[],[f607,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f110,f73])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f85,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f607,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ spl11_2
    | ~ spl11_41 ),
    inference(backward_demodulation,[],[f142,f606])).

fof(f606,plain,
    ( k1_xboole_0 = k1_relat_1(sK5)
    | ~ spl11_41 ),
    inference(resolution,[],[f487,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f79,f77])).

fof(f487,plain,
    ( v1_xboole_0(k1_relat_1(sK5))
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl11_41
  <=> v1_xboole_0(k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f142,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f136,f140])).

fof(f140,plain,(
    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK2
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK2
                & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                & m1_subset_1(X5,sK2) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X3,sK2,sK3)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5))
              & k1_xboole_0 != sK2
              & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4))
              & m1_subset_1(X5,sK2) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5))
            & k1_xboole_0 != sK2
            & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4))
            & m1_subset_1(X5,sK2) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5))
          & k1_xboole_0 != sK2
          & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
          & m1_subset_1(X5,sK2) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5))
        & k1_xboole_0 != sK2
        & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
        & m1_subset_1(X5,sK2) )
   => ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))
      & k1_xboole_0 != sK2
      & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
      & m1_subset_1(sK6,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f136,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl11_2
  <=> r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f392,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK4))
    | ~ spl11_20 ),
    inference(resolution,[],[f291,f77])).

fof(f291,plain,
    ( r2_hidden(sK7(sK2,sK3,sK4),k2_relat_1(sK4))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl11_20
  <=> r2_hidden(sK7(sK2,sK3,sK4),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f645,plain,
    ( spl11_16
    | ~ spl11_46
    | ~ spl11_47 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | spl11_16
    | ~ spl11_46
    | ~ spl11_47 ),
    inference(resolution,[],[f639,f274])).

fof(f639,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_46
    | ~ spl11_47 ),
    inference(forward_demodulation,[],[f541,f560])).

fof(f541,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl11_46
  <=> v1_xboole_0(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f604,plain,
    ( spl11_16
    | ~ spl11_34 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl11_16
    | ~ spl11_34 ),
    inference(resolution,[],[f588,f73])).

fof(f588,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl11_16
    | ~ spl11_34 ),
    inference(backward_demodulation,[],[f274,f430])).

fof(f430,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl11_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f580,plain,
    ( spl11_45
    | ~ spl11_47 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl11_45
    | ~ spl11_47 ),
    inference(resolution,[],[f574,f69])).

fof(f69,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f574,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | spl11_45
    | ~ spl11_47 ),
    inference(backward_demodulation,[],[f537,f560])).

fof(f537,plain,
    ( ~ m1_subset_1(sK6,k1_relat_1(sK4))
    | spl11_45 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl11_45
  <=> m1_subset_1(sK6,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f562,plain,
    ( ~ spl11_18
    | spl11_47
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f556,f509,f558,f281])).

fof(f281,plain,
    ( spl11_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f509,plain,
    ( spl11_44
  <=> sK2 = k1_relset_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f556,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_44 ),
    inference(superposition,[],[f89,f511])).

fof(f511,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f509])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f549,plain,
    ( ~ spl11_2
    | spl11_43 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl11_2
    | spl11_43 ),
    inference(resolution,[],[f502,f142])).

fof(f502,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | spl11_43 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl11_43
  <=> r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f542,plain,
    ( ~ spl11_45
    | spl11_46
    | spl11_42 ),
    inference(avatar_split_clause,[],[f533,f496,f539,f535])).

fof(f496,plain,
    ( spl11_42
  <=> r2_hidden(sK6,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f533,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ m1_subset_1(sK6,k1_relat_1(sK4))
    | spl11_42 ),
    inference(resolution,[],[f498,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f498,plain,
    ( ~ r2_hidden(sK6,k1_relat_1(sK4))
    | spl11_42 ),
    inference(avatar_component_clause,[],[f496])).

fof(f529,plain,(
    ~ spl11_25 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl11_25 ),
    inference(resolution,[],[f513,f73])).

fof(f513,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl11_25 ),
    inference(backward_demodulation,[],[f63,f332])).

fof(f332,plain,
    ( k1_xboole_0 = sK3
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl11_25
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f63,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f512,plain,
    ( ~ spl11_18
    | spl11_44
    | spl11_25 ),
    inference(avatar_split_clause,[],[f506,f330,f509,f281])).

fof(f506,plain,
    ( k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f196,f65])).

fof(f65,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X1,X2,X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f93,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f503,plain,
    ( ~ spl11_42
    | ~ spl11_43
    | ~ spl11_7
    | spl11_40 ),
    inference(avatar_split_clause,[],[f494,f481,f177,f500,f496])).

fof(f177,plain,
    ( spl11_7
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X3,k1_relat_1(sK4))
        | ~ r1_tarski(k2_relat_1(sK4),X4)
        | m1_subset_1(k1_funct_1(sK4,X3),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f481,plain,
    ( spl11_40
  <=> m1_subset_1(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f494,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ r2_hidden(sK6,k1_relat_1(sK4))
    | ~ spl11_7
    | spl11_40 ),
    inference(resolution,[],[f483,f178])).

fof(f178,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(k1_funct_1(sK4,X3),X4)
        | ~ r1_tarski(k2_relat_1(sK4),X4)
        | ~ r2_hidden(X3,k1_relat_1(sK4)) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f177])).

fof(f483,plain,
    ( ~ m1_subset_1(k1_funct_1(sK4,sK6),k1_relat_1(sK5))
    | spl11_40 ),
    inference(avatar_component_clause,[],[f481])).

fof(f490,plain,(
    spl11_37 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl11_37 ),
    inference(resolution,[],[f466,f68])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f466,plain,
    ( ! [X0] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl11_37 ),
    inference(resolution,[],[f460,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f460,plain,
    ( ~ v5_relat_1(sK5,sK1)
    | spl11_37 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl11_37
  <=> v5_relat_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f488,plain,
    ( ~ spl11_40
    | spl11_41
    | spl11_38 ),
    inference(avatar_split_clause,[],[f479,f462,f485,f481])).

fof(f462,plain,
    ( spl11_38
  <=> r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f479,plain,
    ( v1_xboole_0(k1_relat_1(sK5))
    | ~ m1_subset_1(k1_funct_1(sK4,sK6),k1_relat_1(sK5))
    | spl11_38 ),
    inference(resolution,[],[f464,f83])).

fof(f464,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5))
    | spl11_38 ),
    inference(avatar_component_clause,[],[f462])).

fof(f465,plain,
    ( ~ spl11_5
    | ~ spl11_37
    | ~ spl11_32
    | ~ spl11_38
    | spl11_35 ),
    inference(avatar_split_clause,[],[f456,f432,f462,f420,f458,f157])).

fof(f157,plain,
    ( spl11_5
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f420,plain,
    ( spl11_32
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f432,plain,
    ( spl11_35
  <=> k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f456,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v5_relat_1(sK5,sK1)
    | ~ v1_relat_1(sK5)
    | spl11_35 ),
    inference(trivial_inequality_removal,[],[f455])).

fof(f455,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | ~ r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v5_relat_1(sK5,sK1)
    | ~ v1_relat_1(sK5)
    | spl11_35 ),
    inference(superposition,[],[f434,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f434,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | spl11_35 ),
    inference(avatar_component_clause,[],[f432])).

fof(f454,plain,(
    spl11_36 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | spl11_36 ),
    inference(resolution,[],[f438,f143])).

fof(f143,plain,(
    r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(backward_demodulation,[],[f70,f140])).

fof(f70,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f438,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))
    | spl11_36 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl11_36
  <=> r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f448,plain,(
    spl11_31 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl11_31 ),
    inference(resolution,[],[f418,f65])).

fof(f418,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | spl11_31 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl11_31
  <=> v1_funct_2(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f445,plain,(
    spl11_33 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | spl11_33 ),
    inference(resolution,[],[f426,f69])).

fof(f426,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | spl11_33 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl11_33
  <=> m1_subset_1(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f443,plain,(
    spl11_32 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl11_32 ),
    inference(resolution,[],[f422,f67])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f422,plain,
    ( ~ v1_funct_1(sK5)
    | spl11_32 ),
    inference(avatar_component_clause,[],[f420])).

fof(f441,plain,(
    spl11_30 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl11_30 ),
    inference(resolution,[],[f414,f64])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f414,plain,
    ( ~ v1_funct_1(sK4)
    | spl11_30 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl11_30
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f439,plain,
    ( spl11_17
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_18
    | ~ spl11_32
    | ~ spl11_1
    | ~ spl11_33
    | spl11_34
    | ~ spl11_35
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f410,f436,f432,f428,f424,f130,f420,f281,f416,f412,f277])).

fof(f277,plain,
    ( spl11_17
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f130,plain,
    ( spl11_1
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f410,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))
    | k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK3) ),
    inference(forward_demodulation,[],[f409,f140])).

fof(f409,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | k1_xboole_0 = sK2
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ m1_subset_1(sK6,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK3) ),
    inference(superposition,[],[f72,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f72,plain,(
    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f46])).

fof(f381,plain,
    ( ~ spl11_18
    | spl11_28
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f375,f285,f377,f281])).

fof(f285,plain,
    ( spl11_19
  <=> k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f375,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_19 ),
    inference(superposition,[],[f89,f287])).

fof(f287,plain,
    ( k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f285])).

fof(f371,plain,(
    ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl11_16 ),
    inference(trivial_inequality_removal,[],[f369])).

fof(f369,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl11_16 ),
    inference(superposition,[],[f71,f359])).

fof(f359,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_16 ),
    inference(resolution,[],[f275,f107])).

fof(f275,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f71,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

fof(f357,plain,(
    spl11_18 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl11_18 ),
    inference(resolution,[],[f283,f66])).

fof(f283,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f281])).

fof(f309,plain,(
    ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl11_17 ),
    inference(resolution,[],[f279,f63])).

fof(f279,plain,
    ( v1_xboole_0(sK3)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f277])).

fof(f292,plain,
    ( spl11_16
    | spl11_17
    | ~ spl11_18
    | spl11_19
    | spl11_20 ),
    inference(avatar_split_clause,[],[f270,f289,f285,f281,f277,f273])).

fof(f270,plain,
    ( r2_hidden(sK7(sK2,sK3,sK4),k2_relat_1(sK4))
    | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f75,f140])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k2_relset_1(X0,X1,X2))
      | k1_xboole_0 = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(sK7(X0,X1,X2),k2_relset_1(X0,X1,X2))
                & m1_subset_1(sK7(X0,X1,X2),X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
          & m1_subset_1(X3,X1) )
     => ( r2_hidden(sK7(X0,X1,X2),k2_relset_1(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  & m1_subset_1(X3,X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  & m1_subset_1(X3,X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f179,plain,
    ( ~ spl11_3
    | spl11_7
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f175,f153,f177,f149])).

fof(f149,plain,
    ( spl11_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f153,plain,
    ( spl11_4
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK4))
        | ~ v5_relat_1(sK4,X1)
        | m1_subset_1(k1_funct_1(sK4,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f175,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK4))
        | m1_subset_1(k1_funct_1(sK4,X3),X4)
        | ~ r1_tarski(k2_relat_1(sK4),X4)
        | ~ v1_relat_1(sK4) )
    | ~ spl11_4 ),
    inference(resolution,[],[f154,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK4,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | m1_subset_1(k1_funct_1(sK4,X0),X1) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f173,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl11_5 ),
    inference(resolution,[],[f170,f80])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f170,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | spl11_5 ),
    inference(resolution,[],[f165,f68])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl11_5 ),
    inference(resolution,[],[f159,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f159,plain,
    ( ~ v1_relat_1(sK5)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f169,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl11_3 ),
    inference(resolution,[],[f166,f80])).

fof(f166,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | spl11_3 ),
    inference(resolution,[],[f164,f66])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl11_3 ),
    inference(resolution,[],[f151,f76])).

fof(f151,plain,
    ( ~ v1_relat_1(sK4)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f155,plain,
    ( ~ spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f146,f153,f149])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | m1_subset_1(k1_funct_1(sK4,X0),X1)
      | ~ v5_relat_1(sK4,X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f100,f64])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f139,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl11_1 ),
    inference(resolution,[],[f132,f68])).

fof(f132,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f137,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f128,f134,f130])).

fof(f128,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(superposition,[],[f70,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (5592)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (5595)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (5587)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5595)Refutation not found, incomplete strategy% (5595)------------------------------
% 0.20/0.51  % (5595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5603)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (5600)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (5608)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (5595)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5595)Memory used [KB]: 10874
% 0.20/0.52  % (5595)Time elapsed: 0.101 s
% 0.20/0.52  % (5595)------------------------------
% 0.20/0.52  % (5595)------------------------------
% 0.20/0.53  % (5589)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.53  % (5586)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (5614)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.53  % (5588)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (5613)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.54  % (5591)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (5590)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (5585)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (5596)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (5605)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (5607)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (5597)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.55  % (5610)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.55  % (5606)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.55  % (5612)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.55  % (5599)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.55  % (5602)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.55  % (5598)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.55  % (5602)Refutation not found, incomplete strategy% (5602)------------------------------
% 1.48/0.55  % (5602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (5602)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (5602)Memory used [KB]: 10746
% 1.48/0.55  % (5602)Time elapsed: 0.144 s
% 1.48/0.55  % (5602)------------------------------
% 1.48/0.55  % (5602)------------------------------
% 1.48/0.55  % (5611)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (5604)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.56  % (5593)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.56  % (5594)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.56  % (5609)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.57  % (5607)Refutation not found, incomplete strategy% (5607)------------------------------
% 1.48/0.57  % (5607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (5607)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (5607)Memory used [KB]: 11129
% 1.48/0.57  % (5607)Time elapsed: 0.128 s
% 1.48/0.57  % (5607)------------------------------
% 1.48/0.57  % (5607)------------------------------
% 1.48/0.57  % (5606)Refutation not found, incomplete strategy% (5606)------------------------------
% 1.48/0.57  % (5606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (5606)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (5606)Memory used [KB]: 1918
% 1.48/0.57  % (5606)Time elapsed: 0.153 s
% 1.48/0.57  % (5606)------------------------------
% 1.48/0.57  % (5606)------------------------------
% 1.48/0.57  % (5601)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.58  % (5597)Refutation found. Thanks to Tanya!
% 1.48/0.58  % SZS status Theorem for theBenchmark
% 1.48/0.58  % SZS output start Proof for theBenchmark
% 1.48/0.58  fof(f709,plain,(
% 1.48/0.58    $false),
% 1.48/0.58    inference(avatar_sat_refutation,[],[f137,f139,f155,f169,f173,f179,f292,f309,f357,f371,f381,f439,f441,f443,f445,f448,f454,f465,f488,f490,f503,f512,f529,f542,f549,f562,f580,f604,f645,f675,f708])).
% 1.48/0.58  fof(f708,plain,(
% 1.48/0.58    spl11_16 | ~spl11_28 | ~spl11_47),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f707])).
% 1.48/0.58  fof(f707,plain,(
% 1.48/0.58    $false | (spl11_16 | ~spl11_28 | ~spl11_47)),
% 1.48/0.58    inference(resolution,[],[f688,f73])).
% 1.48/0.58  fof(f73,plain,(
% 1.48/0.58    v1_xboole_0(k1_xboole_0)),
% 1.48/0.58    inference(cnf_transformation,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    v1_xboole_0(k1_xboole_0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.58  fof(f688,plain,(
% 1.48/0.58    ~v1_xboole_0(k1_xboole_0) | (spl11_16 | ~spl11_28 | ~spl11_47)),
% 1.48/0.58    inference(backward_demodulation,[],[f274,f683])).
% 1.48/0.58  fof(f683,plain,(
% 1.48/0.58    k1_xboole_0 = sK2 | (~spl11_28 | ~spl11_47)),
% 1.48/0.58    inference(backward_demodulation,[],[f560,f379])).
% 1.48/0.58  fof(f379,plain,(
% 1.48/0.58    k1_xboole_0 = k1_relat_1(sK4) | ~spl11_28),
% 1.48/0.58    inference(avatar_component_clause,[],[f377])).
% 1.48/0.58  fof(f377,plain,(
% 1.48/0.58    spl11_28 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 1.48/0.58  fof(f560,plain,(
% 1.48/0.58    sK2 = k1_relat_1(sK4) | ~spl11_47),
% 1.48/0.58    inference(avatar_component_clause,[],[f558])).
% 1.48/0.58  fof(f558,plain,(
% 1.48/0.58    spl11_47 <=> sK2 = k1_relat_1(sK4)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).
% 1.48/0.58  fof(f274,plain,(
% 1.48/0.58    ~v1_xboole_0(sK2) | spl11_16),
% 1.48/0.58    inference(avatar_component_clause,[],[f273])).
% 1.48/0.58  fof(f273,plain,(
% 1.48/0.58    spl11_16 <=> v1_xboole_0(sK2)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 1.48/0.58  fof(f675,plain,(
% 1.48/0.58    ~spl11_2 | ~spl11_20 | ~spl11_41),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f674])).
% 1.48/0.58  fof(f674,plain,(
% 1.48/0.58    $false | (~spl11_2 | ~spl11_20 | ~spl11_41)),
% 1.48/0.58    inference(resolution,[],[f661,f73])).
% 1.48/0.58  fof(f661,plain,(
% 1.48/0.58    ~v1_xboole_0(k1_xboole_0) | (~spl11_2 | ~spl11_20 | ~spl11_41)),
% 1.48/0.58    inference(backward_demodulation,[],[f392,f632])).
% 1.48/0.58  fof(f632,plain,(
% 1.48/0.58    k1_xboole_0 = k2_relat_1(sK4) | (~spl11_2 | ~spl11_41)),
% 1.48/0.58    inference(resolution,[],[f628,f79])).
% 1.48/0.58  fof(f79,plain,(
% 1.48/0.58    ( ! [X0] : (r2_hidden(sK9(X0),X0) | k1_xboole_0 = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f54])).
% 1.48/0.58  fof(f54,plain,(
% 1.48/0.58    ! [X0] : (r2_hidden(sK9(X0),X0) | k1_xboole_0 = X0)),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f53])).
% 1.48/0.58  fof(f53,plain,(
% 1.48/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f24,plain,(
% 1.48/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.48/0.58    inference(ennf_transformation,[],[f4])).
% 1.48/0.58  fof(f4,axiom,(
% 1.48/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.48/0.58  fof(f628,plain,(
% 1.48/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK4))) ) | (~spl11_2 | ~spl11_41)),
% 1.48/0.58    inference(resolution,[],[f607,f111])).
% 1.48/0.58  fof(f111,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.48/0.58    inference(resolution,[],[f110,f73])).
% 1.48/0.58  fof(f110,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1)) )),
% 1.48/0.58    inference(resolution,[],[f85,f77])).
% 1.48/0.58  fof(f77,plain,(
% 1.48/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f52])).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).
% 1.48/0.58  fof(f51,plain,(
% 1.48/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f50,plain,(
% 1.48/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.48/0.58    inference(rectify,[],[f49])).
% 1.48/0.58  fof(f49,plain,(
% 1.48/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.48/0.58    inference(nnf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.48/0.58  fof(f85,plain,(
% 1.48/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f59])).
% 1.48/0.58  fof(f59,plain,(
% 1.48/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f57,f58])).
% 1.48/0.58  fof(f58,plain,(
% 1.48/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f57,plain,(
% 1.48/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.58    inference(rectify,[],[f56])).
% 1.48/0.58  fof(f56,plain,(
% 1.48/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.58    inference(nnf_transformation,[],[f30])).
% 1.48/0.58  fof(f30,plain,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.58  fof(f607,plain,(
% 1.48/0.58    r1_tarski(k2_relat_1(sK4),k1_xboole_0) | (~spl11_2 | ~spl11_41)),
% 1.48/0.58    inference(backward_demodulation,[],[f142,f606])).
% 1.48/0.58  fof(f606,plain,(
% 1.48/0.58    k1_xboole_0 = k1_relat_1(sK5) | ~spl11_41),
% 1.48/0.58    inference(resolution,[],[f487,f107])).
% 1.48/0.58  fof(f107,plain,(
% 1.48/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.48/0.58    inference(resolution,[],[f79,f77])).
% 1.48/0.58  fof(f487,plain,(
% 1.48/0.58    v1_xboole_0(k1_relat_1(sK5)) | ~spl11_41),
% 1.48/0.58    inference(avatar_component_clause,[],[f485])).
% 1.48/0.58  fof(f485,plain,(
% 1.48/0.58    spl11_41 <=> v1_xboole_0(k1_relat_1(sK5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).
% 1.48/0.58  fof(f142,plain,(
% 1.48/0.58    r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) | ~spl11_2),
% 1.48/0.58    inference(backward_demodulation,[],[f136,f140])).
% 1.48/0.58  fof(f140,plain,(
% 1.48/0.58    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)),
% 1.48/0.58    inference(resolution,[],[f90,f66])).
% 1.48/0.58  fof(f66,plain,(
% 1.48/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f46,plain,(
% 1.48/0.58    (((k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f45,f44,f43,f42])).
% 1.48/0.58  fof(f42,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f43,plain,(
% 1.48/0.58    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f44,plain,(
% 1.48/0.58    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(X5,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f45,plain,(
% 1.48/0.58    ? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(X5,sK2)) => (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f20,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.48/0.58    inference(flattening,[],[f19])).
% 1.48/0.58  fof(f19,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.48/0.58    inference(ennf_transformation,[],[f18])).
% 1.48/0.58  fof(f18,negated_conjecture,(
% 1.48/0.58    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.48/0.58    inference(negated_conjecture,[],[f17])).
% 1.48/0.58  fof(f17,conjecture,(
% 1.48/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 1.48/0.58  fof(f90,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f34])).
% 1.48/0.58  fof(f34,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f12])).
% 1.48/0.58  fof(f12,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.58  fof(f136,plain,(
% 1.48/0.58    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) | ~spl11_2),
% 1.48/0.58    inference(avatar_component_clause,[],[f134])).
% 1.48/0.58  fof(f134,plain,(
% 1.48/0.58    spl11_2 <=> r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.48/0.58  fof(f392,plain,(
% 1.48/0.58    ~v1_xboole_0(k2_relat_1(sK4)) | ~spl11_20),
% 1.48/0.58    inference(resolution,[],[f291,f77])).
% 1.48/0.58  fof(f291,plain,(
% 1.48/0.58    r2_hidden(sK7(sK2,sK3,sK4),k2_relat_1(sK4)) | ~spl11_20),
% 1.48/0.58    inference(avatar_component_clause,[],[f289])).
% 1.48/0.58  fof(f289,plain,(
% 1.48/0.58    spl11_20 <=> r2_hidden(sK7(sK2,sK3,sK4),k2_relat_1(sK4))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 1.48/0.58  fof(f645,plain,(
% 1.48/0.58    spl11_16 | ~spl11_46 | ~spl11_47),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f642])).
% 1.48/0.58  fof(f642,plain,(
% 1.48/0.58    $false | (spl11_16 | ~spl11_46 | ~spl11_47)),
% 1.48/0.58    inference(resolution,[],[f639,f274])).
% 1.48/0.58  fof(f639,plain,(
% 1.48/0.58    v1_xboole_0(sK2) | (~spl11_46 | ~spl11_47)),
% 1.48/0.58    inference(forward_demodulation,[],[f541,f560])).
% 1.48/0.58  fof(f541,plain,(
% 1.48/0.58    v1_xboole_0(k1_relat_1(sK4)) | ~spl11_46),
% 1.48/0.58    inference(avatar_component_clause,[],[f539])).
% 1.48/0.58  fof(f539,plain,(
% 1.48/0.58    spl11_46 <=> v1_xboole_0(k1_relat_1(sK4))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).
% 1.48/0.58  fof(f604,plain,(
% 1.48/0.58    spl11_16 | ~spl11_34),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f603])).
% 1.48/0.58  fof(f603,plain,(
% 1.48/0.58    $false | (spl11_16 | ~spl11_34)),
% 1.48/0.58    inference(resolution,[],[f588,f73])).
% 1.48/0.58  fof(f588,plain,(
% 1.48/0.58    ~v1_xboole_0(k1_xboole_0) | (spl11_16 | ~spl11_34)),
% 1.48/0.58    inference(backward_demodulation,[],[f274,f430])).
% 1.48/0.58  fof(f430,plain,(
% 1.48/0.58    k1_xboole_0 = sK2 | ~spl11_34),
% 1.48/0.58    inference(avatar_component_clause,[],[f428])).
% 1.48/0.58  fof(f428,plain,(
% 1.48/0.58    spl11_34 <=> k1_xboole_0 = sK2),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 1.48/0.58  fof(f580,plain,(
% 1.48/0.58    spl11_45 | ~spl11_47),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f579])).
% 1.48/0.58  fof(f579,plain,(
% 1.48/0.58    $false | (spl11_45 | ~spl11_47)),
% 1.48/0.58    inference(resolution,[],[f574,f69])).
% 1.48/0.58  fof(f69,plain,(
% 1.48/0.58    m1_subset_1(sK6,sK2)),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f574,plain,(
% 1.48/0.58    ~m1_subset_1(sK6,sK2) | (spl11_45 | ~spl11_47)),
% 1.48/0.58    inference(backward_demodulation,[],[f537,f560])).
% 1.48/0.58  fof(f537,plain,(
% 1.48/0.58    ~m1_subset_1(sK6,k1_relat_1(sK4)) | spl11_45),
% 1.48/0.58    inference(avatar_component_clause,[],[f535])).
% 1.48/0.58  fof(f535,plain,(
% 1.48/0.58    spl11_45 <=> m1_subset_1(sK6,k1_relat_1(sK4))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).
% 1.48/0.58  fof(f562,plain,(
% 1.48/0.58    ~spl11_18 | spl11_47 | ~spl11_44),
% 1.48/0.58    inference(avatar_split_clause,[],[f556,f509,f558,f281])).
% 1.48/0.58  fof(f281,plain,(
% 1.48/0.58    spl11_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.48/0.58  fof(f509,plain,(
% 1.48/0.58    spl11_44 <=> sK2 = k1_relset_1(sK2,sK3,sK4)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).
% 1.48/0.58  fof(f556,plain,(
% 1.48/0.58    sK2 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl11_44),
% 1.48/0.58    inference(superposition,[],[f89,f511])).
% 1.48/0.58  fof(f511,plain,(
% 1.48/0.58    sK2 = k1_relset_1(sK2,sK3,sK4) | ~spl11_44),
% 1.48/0.58    inference(avatar_component_clause,[],[f509])).
% 1.48/0.58  fof(f89,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f33])).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.48/0.58  fof(f549,plain,(
% 1.48/0.58    ~spl11_2 | spl11_43),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f545])).
% 1.48/0.58  fof(f545,plain,(
% 1.48/0.58    $false | (~spl11_2 | spl11_43)),
% 1.48/0.58    inference(resolution,[],[f502,f142])).
% 1.48/0.58  fof(f502,plain,(
% 1.48/0.58    ~r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) | spl11_43),
% 1.48/0.58    inference(avatar_component_clause,[],[f500])).
% 1.48/0.58  fof(f500,plain,(
% 1.48/0.58    spl11_43 <=> r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).
% 1.48/0.58  fof(f542,plain,(
% 1.48/0.58    ~spl11_45 | spl11_46 | spl11_42),
% 1.48/0.58    inference(avatar_split_clause,[],[f533,f496,f539,f535])).
% 1.48/0.58  fof(f496,plain,(
% 1.48/0.58    spl11_42 <=> r2_hidden(sK6,k1_relat_1(sK4))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).
% 1.48/0.58  fof(f533,plain,(
% 1.48/0.58    v1_xboole_0(k1_relat_1(sK4)) | ~m1_subset_1(sK6,k1_relat_1(sK4)) | spl11_42),
% 1.48/0.58    inference(resolution,[],[f498,f83])).
% 1.48/0.58  fof(f83,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f27])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.48/0.58    inference(flattening,[],[f26])).
% 1.48/0.58  fof(f26,plain,(
% 1.48/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.48/0.58    inference(ennf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.48/0.58  fof(f498,plain,(
% 1.48/0.58    ~r2_hidden(sK6,k1_relat_1(sK4)) | spl11_42),
% 1.48/0.58    inference(avatar_component_clause,[],[f496])).
% 1.48/0.58  fof(f529,plain,(
% 1.48/0.58    ~spl11_25),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f528])).
% 1.48/0.58  fof(f528,plain,(
% 1.48/0.58    $false | ~spl11_25),
% 1.48/0.58    inference(resolution,[],[f513,f73])).
% 1.48/0.58  fof(f513,plain,(
% 1.48/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl11_25),
% 1.48/0.58    inference(backward_demodulation,[],[f63,f332])).
% 1.48/0.58  fof(f332,plain,(
% 1.48/0.58    k1_xboole_0 = sK3 | ~spl11_25),
% 1.48/0.58    inference(avatar_component_clause,[],[f330])).
% 1.48/0.58  fof(f330,plain,(
% 1.48/0.58    spl11_25 <=> k1_xboole_0 = sK3),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 1.48/0.58  fof(f63,plain,(
% 1.48/0.58    ~v1_xboole_0(sK3)),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f512,plain,(
% 1.48/0.58    ~spl11_18 | spl11_44 | spl11_25),
% 1.48/0.58    inference(avatar_split_clause,[],[f506,f330,f509,f281])).
% 1.48/0.58  fof(f506,plain,(
% 1.48/0.58    k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.48/0.58    inference(resolution,[],[f196,f65])).
% 1.48/0.58  fof(f65,plain,(
% 1.48/0.58    v1_funct_2(sK4,sK2,sK3)),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f196,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X0,X1,X2) | k1_xboole_0 = X2 | k1_relset_1(X1,X2,X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.48/0.58    inference(resolution,[],[f93,f97])).
% 1.48/0.58  fof(f97,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f62])).
% 1.48/0.58  fof(f62,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(nnf_transformation,[],[f41])).
% 1.48/0.58  fof(f41,plain,(
% 1.48/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(definition_folding,[],[f37,f40])).
% 1.48/0.58  fof(f40,plain,(
% 1.48/0.58    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.48/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.58  fof(f37,plain,(
% 1.48/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(flattening,[],[f36])).
% 1.48/0.58  fof(f36,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f14])).
% 1.48/0.58  fof(f14,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.48/0.58  fof(f93,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f61])).
% 1.48/0.58  fof(f61,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.48/0.58    inference(rectify,[],[f60])).
% 1.48/0.58  fof(f60,plain,(
% 1.48/0.58    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.48/0.58    inference(nnf_transformation,[],[f40])).
% 1.48/0.58  fof(f503,plain,(
% 1.48/0.58    ~spl11_42 | ~spl11_43 | ~spl11_7 | spl11_40),
% 1.48/0.58    inference(avatar_split_clause,[],[f494,f481,f177,f500,f496])).
% 1.48/0.58  fof(f177,plain,(
% 1.48/0.58    spl11_7 <=> ! [X3,X4] : (~r2_hidden(X3,k1_relat_1(sK4)) | ~r1_tarski(k2_relat_1(sK4),X4) | m1_subset_1(k1_funct_1(sK4,X3),X4))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.48/0.58  fof(f481,plain,(
% 1.48/0.58    spl11_40 <=> m1_subset_1(k1_funct_1(sK4,sK6),k1_relat_1(sK5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).
% 1.48/0.58  fof(f494,plain,(
% 1.48/0.58    ~r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) | ~r2_hidden(sK6,k1_relat_1(sK4)) | (~spl11_7 | spl11_40)),
% 1.48/0.58    inference(resolution,[],[f483,f178])).
% 1.48/0.58  fof(f178,plain,(
% 1.48/0.58    ( ! [X4,X3] : (m1_subset_1(k1_funct_1(sK4,X3),X4) | ~r1_tarski(k2_relat_1(sK4),X4) | ~r2_hidden(X3,k1_relat_1(sK4))) ) | ~spl11_7),
% 1.48/0.58    inference(avatar_component_clause,[],[f177])).
% 1.48/0.58  fof(f483,plain,(
% 1.48/0.58    ~m1_subset_1(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) | spl11_40),
% 1.48/0.58    inference(avatar_component_clause,[],[f481])).
% 1.48/0.58  fof(f490,plain,(
% 1.48/0.58    spl11_37),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f489])).
% 1.48/0.58  fof(f489,plain,(
% 1.48/0.58    $false | spl11_37),
% 1.48/0.58    inference(resolution,[],[f466,f68])).
% 1.48/0.58  fof(f68,plain,(
% 1.48/0.58    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f466,plain,(
% 1.48/0.58    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl11_37),
% 1.48/0.58    inference(resolution,[],[f460,f92])).
% 1.48/0.58  fof(f92,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f35])).
% 1.48/0.58  fof(f35,plain,(
% 1.48/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f10])).
% 1.48/0.58  fof(f10,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.48/0.58  fof(f460,plain,(
% 1.48/0.58    ~v5_relat_1(sK5,sK1) | spl11_37),
% 1.48/0.58    inference(avatar_component_clause,[],[f458])).
% 1.48/0.58  fof(f458,plain,(
% 1.48/0.58    spl11_37 <=> v5_relat_1(sK5,sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).
% 1.48/0.58  fof(f488,plain,(
% 1.48/0.58    ~spl11_40 | spl11_41 | spl11_38),
% 1.48/0.58    inference(avatar_split_clause,[],[f479,f462,f485,f481])).
% 1.48/0.58  fof(f462,plain,(
% 1.48/0.58    spl11_38 <=> r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).
% 1.48/0.58  fof(f479,plain,(
% 1.48/0.58    v1_xboole_0(k1_relat_1(sK5)) | ~m1_subset_1(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) | spl11_38),
% 1.48/0.58    inference(resolution,[],[f464,f83])).
% 1.48/0.58  fof(f464,plain,(
% 1.48/0.58    ~r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) | spl11_38),
% 1.48/0.58    inference(avatar_component_clause,[],[f462])).
% 1.48/0.58  fof(f465,plain,(
% 1.48/0.58    ~spl11_5 | ~spl11_37 | ~spl11_32 | ~spl11_38 | spl11_35),
% 1.48/0.58    inference(avatar_split_clause,[],[f456,f432,f462,f420,f458,f157])).
% 1.48/0.58  fof(f157,plain,(
% 1.48/0.58    spl11_5 <=> v1_relat_1(sK5)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.48/0.58  fof(f420,plain,(
% 1.48/0.58    spl11_32 <=> v1_funct_1(sK5)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 1.48/0.58  fof(f432,plain,(
% 1.48/0.58    spl11_35 <=> k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 1.48/0.58  fof(f456,plain,(
% 1.48/0.58    ~r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v5_relat_1(sK5,sK1) | ~v1_relat_1(sK5) | spl11_35),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f455])).
% 1.48/0.58  fof(f455,plain,(
% 1.48/0.58    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) | ~r2_hidden(k1_funct_1(sK4,sK6),k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v5_relat_1(sK5,sK1) | ~v1_relat_1(sK5) | spl11_35),
% 1.48/0.58    inference(superposition,[],[f434,f84])).
% 1.48/0.58  fof(f84,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f29])).
% 1.48/0.58  fof(f29,plain,(
% 1.48/0.58    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.48/0.58    inference(flattening,[],[f28])).
% 1.48/0.58  fof(f28,plain,(
% 1.48/0.58    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f15])).
% 1.48/0.58  fof(f15,axiom,(
% 1.48/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 1.48/0.58  fof(f434,plain,(
% 1.48/0.58    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) | spl11_35),
% 1.48/0.58    inference(avatar_component_clause,[],[f432])).
% 1.48/0.58  fof(f454,plain,(
% 1.48/0.58    spl11_36),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f449])).
% 1.48/0.58  fof(f449,plain,(
% 1.48/0.58    $false | spl11_36),
% 1.48/0.58    inference(resolution,[],[f438,f143])).
% 1.48/0.58  fof(f143,plain,(
% 1.48/0.58    r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))),
% 1.48/0.58    inference(backward_demodulation,[],[f70,f140])).
% 1.48/0.58  fof(f70,plain,(
% 1.48/0.58    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f438,plain,(
% 1.48/0.58    ~r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) | spl11_36),
% 1.48/0.58    inference(avatar_component_clause,[],[f436])).
% 1.48/0.58  fof(f436,plain,(
% 1.48/0.58    spl11_36 <=> r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).
% 1.48/0.58  fof(f448,plain,(
% 1.48/0.58    spl11_31),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f446])).
% 1.48/0.58  fof(f446,plain,(
% 1.48/0.58    $false | spl11_31),
% 1.48/0.58    inference(resolution,[],[f418,f65])).
% 1.48/0.58  fof(f418,plain,(
% 1.48/0.58    ~v1_funct_2(sK4,sK2,sK3) | spl11_31),
% 1.48/0.58    inference(avatar_component_clause,[],[f416])).
% 1.48/0.58  fof(f416,plain,(
% 1.48/0.58    spl11_31 <=> v1_funct_2(sK4,sK2,sK3)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 1.48/0.58  fof(f445,plain,(
% 1.48/0.58    spl11_33),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f444])).
% 1.48/0.58  fof(f444,plain,(
% 1.48/0.58    $false | spl11_33),
% 1.48/0.58    inference(resolution,[],[f426,f69])).
% 1.48/0.58  fof(f426,plain,(
% 1.48/0.58    ~m1_subset_1(sK6,sK2) | spl11_33),
% 1.48/0.58    inference(avatar_component_clause,[],[f424])).
% 1.48/0.58  fof(f424,plain,(
% 1.48/0.58    spl11_33 <=> m1_subset_1(sK6,sK2)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 1.48/0.58  fof(f443,plain,(
% 1.48/0.58    spl11_32),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f442])).
% 1.48/0.58  fof(f442,plain,(
% 1.48/0.58    $false | spl11_32),
% 1.48/0.58    inference(resolution,[],[f422,f67])).
% 1.48/0.58  fof(f67,plain,(
% 1.48/0.58    v1_funct_1(sK5)),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f422,plain,(
% 1.48/0.58    ~v1_funct_1(sK5) | spl11_32),
% 1.48/0.58    inference(avatar_component_clause,[],[f420])).
% 1.48/0.58  fof(f441,plain,(
% 1.48/0.58    spl11_30),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f440])).
% 1.48/0.58  fof(f440,plain,(
% 1.48/0.58    $false | spl11_30),
% 1.48/0.58    inference(resolution,[],[f414,f64])).
% 1.48/0.58  fof(f64,plain,(
% 1.48/0.58    v1_funct_1(sK4)),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f414,plain,(
% 1.48/0.58    ~v1_funct_1(sK4) | spl11_30),
% 1.48/0.58    inference(avatar_component_clause,[],[f412])).
% 1.48/0.58  fof(f412,plain,(
% 1.48/0.58    spl11_30 <=> v1_funct_1(sK4)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 1.48/0.58  fof(f439,plain,(
% 1.48/0.58    spl11_17 | ~spl11_30 | ~spl11_31 | ~spl11_18 | ~spl11_32 | ~spl11_1 | ~spl11_33 | spl11_34 | ~spl11_35 | ~spl11_36),
% 1.48/0.58    inference(avatar_split_clause,[],[f410,f436,f432,f428,f424,f130,f420,f281,f416,f412,f277])).
% 1.48/0.58  fof(f277,plain,(
% 1.48/0.58    spl11_17 <=> v1_xboole_0(sK3)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 1.48/0.58  fof(f130,plain,(
% 1.48/0.58    spl11_1 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.48/0.58  fof(f410,plain,(
% 1.48/0.58    ~r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) | k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | v1_xboole_0(sK3)),
% 1.48/0.58    inference(forward_demodulation,[],[f409,f140])).
% 1.48/0.58  fof(f409,plain,(
% 1.48/0.58    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) | k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) | ~m1_subset_1(sK6,sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | v1_xboole_0(sK3)),
% 1.48/0.58    inference(superposition,[],[f72,f88])).
% 1.48/0.58  fof(f88,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f32])).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.48/0.58    inference(flattening,[],[f31])).
% 1.48/0.58  fof(f31,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.48/0.58    inference(ennf_transformation,[],[f16])).
% 1.48/0.58  fof(f16,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 1.48/0.58  fof(f72,plain,(
% 1.48/0.58    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f381,plain,(
% 1.48/0.58    ~spl11_18 | spl11_28 | ~spl11_19),
% 1.48/0.58    inference(avatar_split_clause,[],[f375,f285,f377,f281])).
% 1.48/0.58  fof(f285,plain,(
% 1.48/0.58    spl11_19 <=> k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 1.48/0.58  fof(f375,plain,(
% 1.48/0.58    k1_xboole_0 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl11_19),
% 1.48/0.58    inference(superposition,[],[f89,f287])).
% 1.48/0.58  fof(f287,plain,(
% 1.48/0.58    k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) | ~spl11_19),
% 1.48/0.58    inference(avatar_component_clause,[],[f285])).
% 1.48/0.58  fof(f371,plain,(
% 1.48/0.58    ~spl11_16),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f370])).
% 1.48/0.58  fof(f370,plain,(
% 1.48/0.58    $false | ~spl11_16),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f369])).
% 1.48/0.58  fof(f369,plain,(
% 1.48/0.58    k1_xboole_0 != k1_xboole_0 | ~spl11_16),
% 1.48/0.58    inference(superposition,[],[f71,f359])).
% 1.48/0.58  fof(f359,plain,(
% 1.48/0.58    k1_xboole_0 = sK2 | ~spl11_16),
% 1.48/0.58    inference(resolution,[],[f275,f107])).
% 1.48/0.58  fof(f275,plain,(
% 1.48/0.58    v1_xboole_0(sK2) | ~spl11_16),
% 1.48/0.58    inference(avatar_component_clause,[],[f273])).
% 1.48/0.58  fof(f71,plain,(
% 1.48/0.58    k1_xboole_0 != sK2),
% 1.48/0.58    inference(cnf_transformation,[],[f46])).
% 1.48/0.58  fof(f357,plain,(
% 1.48/0.58    spl11_18),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f356])).
% 1.48/0.58  fof(f356,plain,(
% 1.48/0.58    $false | spl11_18),
% 1.48/0.58    inference(resolution,[],[f283,f66])).
% 1.48/0.58  fof(f283,plain,(
% 1.48/0.58    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | spl11_18),
% 1.48/0.58    inference(avatar_component_clause,[],[f281])).
% 1.48/0.58  fof(f309,plain,(
% 1.48/0.58    ~spl11_17),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f306])).
% 1.48/0.58  fof(f306,plain,(
% 1.48/0.58    $false | ~spl11_17),
% 1.48/0.58    inference(resolution,[],[f279,f63])).
% 1.48/0.58  fof(f279,plain,(
% 1.48/0.58    v1_xboole_0(sK3) | ~spl11_17),
% 1.48/0.58    inference(avatar_component_clause,[],[f277])).
% 1.48/0.58  fof(f292,plain,(
% 1.48/0.58    spl11_16 | spl11_17 | ~spl11_18 | spl11_19 | spl11_20),
% 1.48/0.58    inference(avatar_split_clause,[],[f270,f289,f285,f281,f277,f273])).
% 1.48/0.58  fof(f270,plain,(
% 1.48/0.58    r2_hidden(sK7(sK2,sK3,sK4),k2_relat_1(sK4)) | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 1.48/0.58    inference(superposition,[],[f75,f140])).
% 1.48/0.58  fof(f75,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),k2_relset_1(X0,X1,X2)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f48])).
% 1.48/0.58  fof(f48,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(sK7(X0,X1,X2),k2_relset_1(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f47])).
% 1.48/0.58  fof(f47,plain,(
% 1.48/0.58    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) => (r2_hidden(sK7(X0,X1,X2),k2_relset_1(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),X1)))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f22,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.48/0.58    inference(flattening,[],[f21])).
% 1.48/0.58  fof(f21,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f13])).
% 1.48/0.58  fof(f13,axiom,(
% 1.48/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 1.48/0.58  fof(f179,plain,(
% 1.48/0.58    ~spl11_3 | spl11_7 | ~spl11_4),
% 1.48/0.58    inference(avatar_split_clause,[],[f175,f153,f177,f149])).
% 1.48/0.58  fof(f149,plain,(
% 1.48/0.58    spl11_3 <=> v1_relat_1(sK4)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.48/0.58  fof(f153,plain,(
% 1.48/0.58    spl11_4 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | ~v5_relat_1(sK4,X1) | m1_subset_1(k1_funct_1(sK4,X0),X1))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.48/0.58  fof(f175,plain,(
% 1.48/0.58    ( ! [X4,X3] : (~r2_hidden(X3,k1_relat_1(sK4)) | m1_subset_1(k1_funct_1(sK4,X3),X4) | ~r1_tarski(k2_relat_1(sK4),X4) | ~v1_relat_1(sK4)) ) | ~spl11_4),
% 1.48/0.58    inference(resolution,[],[f154,f82])).
% 1.48/0.58  fof(f82,plain,(
% 1.48/0.58    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f55])).
% 1.48/0.58  fof(f55,plain,(
% 1.48/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.48/0.58    inference(nnf_transformation,[],[f25])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.58    inference(ennf_transformation,[],[f7])).
% 1.48/0.58  fof(f7,axiom,(
% 1.48/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.48/0.58  fof(f154,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~v5_relat_1(sK4,X1) | ~r2_hidden(X0,k1_relat_1(sK4)) | m1_subset_1(k1_funct_1(sK4,X0),X1)) ) | ~spl11_4),
% 1.48/0.58    inference(avatar_component_clause,[],[f153])).
% 1.48/0.58  fof(f173,plain,(
% 1.48/0.58    spl11_5),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f171])).
% 1.48/0.58  fof(f171,plain,(
% 1.48/0.58    $false | spl11_5),
% 1.48/0.58    inference(resolution,[],[f170,f80])).
% 1.48/0.58  fof(f80,plain,(
% 1.48/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f8])).
% 1.48/0.58  fof(f8,axiom,(
% 1.48/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.48/0.58  fof(f170,plain,(
% 1.48/0.58    ~v1_relat_1(k2_zfmisc_1(sK3,sK1)) | spl11_5),
% 1.48/0.58    inference(resolution,[],[f165,f68])).
% 1.48/0.58  fof(f165,plain,(
% 1.48/0.58    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl11_5),
% 1.48/0.58    inference(resolution,[],[f159,f76])).
% 1.48/0.58  fof(f76,plain,(
% 1.48/0.58    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f23])).
% 1.48/0.58  fof(f23,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f6])).
% 1.48/0.58  fof(f6,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.48/0.58  fof(f159,plain,(
% 1.48/0.58    ~v1_relat_1(sK5) | spl11_5),
% 1.48/0.58    inference(avatar_component_clause,[],[f157])).
% 1.48/0.58  fof(f169,plain,(
% 1.48/0.58    spl11_3),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f167])).
% 1.48/0.58  fof(f167,plain,(
% 1.48/0.58    $false | spl11_3),
% 1.48/0.58    inference(resolution,[],[f166,f80])).
% 1.48/0.58  fof(f166,plain,(
% 1.48/0.58    ~v1_relat_1(k2_zfmisc_1(sK2,sK3)) | spl11_3),
% 1.48/0.58    inference(resolution,[],[f164,f66])).
% 1.48/0.58  fof(f164,plain,(
% 1.48/0.58    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl11_3),
% 1.48/0.58    inference(resolution,[],[f151,f76])).
% 1.48/0.58  fof(f151,plain,(
% 1.48/0.58    ~v1_relat_1(sK4) | spl11_3),
% 1.48/0.58    inference(avatar_component_clause,[],[f149])).
% 1.48/0.58  fof(f155,plain,(
% 1.48/0.58    ~spl11_3 | spl11_4),
% 1.48/0.58    inference(avatar_split_clause,[],[f146,f153,f149])).
% 1.48/0.58  fof(f146,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK4)) | m1_subset_1(k1_funct_1(sK4,X0),X1) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) )),
% 1.48/0.58    inference(resolution,[],[f100,f64])).
% 1.48/0.58  fof(f100,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f39])).
% 1.48/0.58  fof(f39,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 1.48/0.58    inference(flattening,[],[f38])).
% 1.48/0.58  fof(f38,plain,(
% 1.48/0.58    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 1.48/0.58    inference(ennf_transformation,[],[f9])).
% 1.48/0.58  fof(f9,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 1.48/0.58  fof(f139,plain,(
% 1.48/0.58    spl11_1),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f138])).
% 1.48/0.58  fof(f138,plain,(
% 1.48/0.58    $false | spl11_1),
% 1.48/0.58    inference(resolution,[],[f132,f68])).
% 1.48/0.58  fof(f132,plain,(
% 1.48/0.58    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | spl11_1),
% 1.48/0.58    inference(avatar_component_clause,[],[f130])).
% 1.48/0.58  fof(f137,plain,(
% 1.48/0.58    ~spl11_1 | spl11_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f128,f134,f130])).
% 1.48/0.58  fof(f128,plain,(
% 1.48/0.58    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.48/0.58    inference(superposition,[],[f70,f89])).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (5597)------------------------------
% 1.48/0.58  % (5597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (5597)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (5597)Memory used [KB]: 6524
% 1.48/0.58  % (5597)Time elapsed: 0.183 s
% 1.48/0.58  % (5597)------------------------------
% 1.48/0.58  % (5597)------------------------------
% 1.48/0.58  % (5589)Refutation not found, incomplete strategy% (5589)------------------------------
% 1.48/0.58  % (5589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (5589)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (5589)Memory used [KB]: 6780
% 1.48/0.58  % (5589)Time elapsed: 0.161 s
% 1.48/0.58  % (5589)------------------------------
% 1.48/0.58  % (5589)------------------------------
% 1.48/0.59  % (5584)Success in time 0.233 s
%------------------------------------------------------------------------------

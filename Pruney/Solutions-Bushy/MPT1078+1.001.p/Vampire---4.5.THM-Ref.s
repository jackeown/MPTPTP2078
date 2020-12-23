%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1078+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:13 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  283 (1475 expanded)
%              Number of leaves         :   34 ( 574 expanded)
%              Depth                    :   23
%              Number of atoms          : 1330 (12577 expanded)
%              Number of equality atoms :   21 ( 127 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1691,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f198,f203,f215,f395,f409,f437,f456,f540,f1265,f1468,f1484,f1505,f1527,f1544,f1622,f1639,f1670,f1681])).

fof(f1681,plain,
    ( ~ spl8_50
    | ~ spl8_62
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | spl8_48 ),
    inference(avatar_split_clause,[],[f1680,f890,f360,f356,f352,f1084,f918])).

fof(f918,plain,
    ( spl8_50
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f1084,plain,
    ( spl8_62
  <=> r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f352,plain,
    ( spl8_21
  <=> v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f356,plain,
    ( spl8_22
  <=> v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f360,plain,
    ( spl8_23
  <=> m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f890,plain,
    ( spl8_48
  <=> r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f1680,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1679,f353])).

fof(f353,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f352])).

fof(f1679,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ spl8_22
    | ~ spl8_23
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1678,f357])).

fof(f357,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f356])).

fof(f1678,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ spl8_23
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1677,f361])).

fof(f361,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f360])).

fof(f1677,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1676,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK5)))
    & r1_tarski(sK4,sK5)
    & r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK6,sK1,sK2)
    & v1_funct_1(sK6)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3,X4,X5] :
                ( ? [X6] :
                    ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                    & r1_tarski(X3,X4)
                    & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X5,X0,X1)
                & v1_funct_1(X5) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X5,X4,X3,X2] :
              ( ? [X6] :
                  ( ~ r2_funct_2(sK1,X2,k8_funct_2(sK1,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(sK1,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(sK1,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
              & v1_funct_2(X5,sK1,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X5,X4,X3,X2] :
            ( ? [X6] :
                ( ~ r2_funct_2(sK1,X2,k8_funct_2(sK1,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(sK1,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                & r1_tarski(X3,X4)
                & r1_tarski(k2_relset_1(sK1,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
            & v1_funct_2(X5,sK1,X1)
            & v1_funct_1(X5) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X5,X4,X3,X2] :
          ( ? [X6] :
              ( ~ r2_funct_2(sK1,X2,k8_funct_2(sK1,sK2,X2,X5,k2_partfun1(sK2,X2,X6,X3)),k8_funct_2(sK1,sK2,X2,X5,k2_partfun1(sK2,X2,X6,X4)))
              & r1_tarski(X3,X4)
              & r1_tarski(k2_relset_1(sK1,sK2,X5),k1_relset_1(sK2,X2,k2_partfun1(sK2,X2,X6,X3)))
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X5,sK1,sK2)
          & v1_funct_1(X5) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X5,X4,X3,X2] :
        ( ? [X6] :
            ( ~ r2_funct_2(sK1,X2,k8_funct_2(sK1,sK2,X2,X5,k2_partfun1(sK2,X2,X6,X3)),k8_funct_2(sK1,sK2,X2,X5,k2_partfun1(sK2,X2,X6,X4)))
            & r1_tarski(X3,X4)
            & r1_tarski(k2_relset_1(sK1,sK2,X5),k1_relset_1(sK2,X2,k2_partfun1(sK2,X2,X6,X3)))
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
            & v1_funct_1(X6) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X5,sK1,sK2)
        & v1_funct_1(X5) )
   => ( ? [X6] :
          ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,X6,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,X6,sK5)))
          & r1_tarski(sK4,sK5)
          & r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,X6,sK4)))
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_1(X6) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK6,sK1,sK2)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X6] :
        ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,X6,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,X6,sK5)))
        & r1_tarski(sK4,sK5)
        & r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,X6,sK4)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_1(X6) )
   => ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK5)))
      & r1_tarski(sK4,sK5)
      & r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3,X4,X5] :
              ( ? [X6] :
                  ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X5,X0,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3,X4,X5] :
              ( ? [X6] :
                  ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X5,X0,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3,X4,X5] :
                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X5,X0,X1)
                  & v1_funct_1(X5) )
               => ! [X6] :
                    ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_1(X6) )
                   => ( ( r1_tarski(X3,X4)
                        & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3))) )
                     => r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3,X4,X5] :
              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X5,X0,X1)
                & v1_funct_1(X5) )
             => ! [X6] :
                  ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_1(X6) )
                 => ( ( r1_tarski(X3,X4)
                      & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3))) )
                   => r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_funct_2)).

fof(f1676,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1675,f49])).

fof(f49,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1675,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1674,f50])).

fof(f50,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f1674,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1673,f51])).

fof(f51,plain,(
    v1_funct_2(sK6,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1673,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1672,f52])).

fof(f52,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f1672,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1671,f53])).

fof(f53,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f1671,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(subsumption_resolution,[],[f1646,f54])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f1646,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(superposition,[],[f892,f433])).

fof(f433,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k8_funct_2(X0,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,k7_relat_1(X4,X5)))
      | ~ m1_subset_1(k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5)),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5)),X0,X3)
      | ~ v1_funct_1(k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f432,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP0(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ sP0(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f432,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,k7_relat_1(X4,X5)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | k8_funct_2(X0,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5))
      | ~ m1_subset_1(k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5)),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5)),X0,X3)
      | ~ v1_funct_1(k8_funct_2(X0,X1,X3,X2,k7_relat_1(X4,X5)))
      | ~ sP0(X3,X0,X4,X2,X1) ) ),
    inference(resolution,[],[f271,f229])).

fof(f229,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r2_funct_2(X6,X7,X8,k8_funct_2(X6,X9,X7,X10,X11))
      | k8_funct_2(X6,X9,X7,X10,X11) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_2(X8,X6,X7)
      | ~ v1_funct_1(X8)
      | ~ sP0(X7,X6,X11,X10,X9) ) ),
    inference(subsumption_resolution,[],[f228,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X1,X4,X0,X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X1,X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k8_funct_2(X1,X4,X0,X3,X2),X1,X0)
        & v1_funct_1(k8_funct_2(X1,X4,X0,X3,X2)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ sP0(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f228,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r2_funct_2(X6,X7,X8,k8_funct_2(X6,X9,X7,X10,X11))
      | k8_funct_2(X6,X9,X7,X10,X11) = X8
      | ~ v1_funct_1(k8_funct_2(X6,X9,X7,X10,X11))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_2(X8,X6,X7)
      | ~ v1_funct_1(X8)
      | ~ sP0(X7,X6,X11,X10,X9) ) ),
    inference(subsumption_resolution,[],[f219,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X1,X4,X0,X3,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f219,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r2_funct_2(X6,X7,X8,k8_funct_2(X6,X9,X7,X10,X11))
      | k8_funct_2(X6,X9,X7,X10,X11) = X8
      | ~ v1_funct_2(k8_funct_2(X6,X9,X7,X10,X11),X6,X7)
      | ~ v1_funct_1(k8_funct_2(X6,X9,X7,X10,X11))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_2(X8,X6,X7)
      | ~ v1_funct_1(X8)
      | ~ sP0(X7,X6,X11,X10,X9) ) ),
    inference(resolution,[],[f67,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X1,X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f271,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(X4,X1,k8_funct_2(X4,X0,X1,X5,k7_relat_1(X2,X3)),k8_funct_2(X4,X0,X1,X5,X2))
      | ~ r1_tarski(k2_relset_1(X4,X0,X5),k1_relset_1(X0,X1,k7_relat_1(X2,X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
      | ~ v1_funct_2(X5,X4,X0)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(X4,X1,k8_funct_2(X4,X0,X1,X5,k7_relat_1(X2,X3)),k8_funct_2(X4,X0,X1,X5,X2))
      | ~ r1_tarski(k2_relset_1(X4,X0,X5),k1_relset_1(X0,X1,k7_relat_1(X2,X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
      | ~ v1_funct_2(X5,X4,X0)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f58,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5))
      | ~ r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3,X4] :
              ( ! [X5] :
                  ( r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5))
                  | ~ r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3,X4] :
              ( ! [X5] :
                  ( r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5))
                  | ~ r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3,X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_1(X5) )
                 => ( r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
                   => r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_funct_2)).

fof(f892,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_48 ),
    inference(avatar_component_clause,[],[f890])).

fof(f1670,plain,
    ( ~ spl8_1
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(subsumption_resolution,[],[f1668,f79])).

fof(f79,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1668,plain,
    ( ~ v1_relat_1(sK7)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(subsumption_resolution,[],[f1666,f56])).

fof(f56,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f1666,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(resolution,[],[f1665,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

fof(f1665,plain,
    ( ~ r1_tarski(k7_relat_1(sK7,sK4),k7_relat_1(sK7,sK5))
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(subsumption_resolution,[],[f1664,f206])).

fof(f206,plain,
    ( v1_relat_1(k7_relat_1(sK7,sK4))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f205,f53])).

fof(f205,plain,
    ( v1_relat_1(k7_relat_1(sK7,sK4))
    | ~ v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f204,f54])).

fof(f204,plain,
    ( v1_relat_1(k7_relat_1(sK7,sK4))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(superposition,[],[f173,f69])).

fof(f173,plain,
    ( v1_relat_1(k2_partfun1(sK2,sK3,sK7,sK4))
    | ~ spl8_1 ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,
    ( m1_subset_1(k2_partfun1(sK2,sK3,sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_1
  <=> m1_subset_1(k2_partfun1(sK2,sK3,sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1664,plain,
    ( ~ r1_tarski(k7_relat_1(sK7,sK4),k7_relat_1(sK7,sK5))
    | ~ v1_relat_1(k7_relat_1(sK7,sK4))
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(subsumption_resolution,[],[f1662,f287])).

fof(f287,plain,(
    ! [X14] : v1_relat_1(k7_relat_1(sK7,X14)) ),
    inference(subsumption_resolution,[],[f281,f53])).

fof(f281,plain,(
    ! [X14] :
      ( ~ v1_funct_1(sK7)
      | v1_relat_1(k7_relat_1(sK7,X14)) ) ),
    inference(resolution,[],[f275,f54])).

fof(f275,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_relat_1(k7_relat_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f154,f69])).

fof(f154,plain,(
    ! [X12,X10,X11,X9] :
      ( v1_relat_1(k2_partfun1(X10,X11,X9,X12))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(resolution,[],[f71,f62])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1662,plain,
    ( ~ r1_tarski(k7_relat_1(sK7,sK4),k7_relat_1(sK7,sK5))
    | ~ v1_relat_1(k7_relat_1(sK7,sK5))
    | ~ v1_relat_1(k7_relat_1(sK7,sK4))
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(resolution,[],[f1658,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1658,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK7,sK4)),k1_relat_1(k7_relat_1(sK7,sK5)))
    | ~ spl8_12
    | ~ spl8_26
    | spl8_50 ),
    inference(resolution,[],[f1462,f202])).

fof(f202,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relat_1(k7_relat_1(sK7,sK4)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_12
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relat_1(k7_relat_1(sK7,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1462,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),X0)
        | ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK7,sK5))) )
    | ~ spl8_26
    | spl8_50 ),
    inference(resolution,[],[f1187,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1187,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relat_1(k7_relat_1(sK7,sK5)))
    | ~ spl8_26
    | spl8_50 ),
    inference(subsumption_resolution,[],[f1185,f521])).

fof(f521,plain,
    ( m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl8_26
  <=> m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1185,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relat_1(k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_50 ),
    inference(superposition,[],[f920,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f920,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK5)))
    | spl8_50 ),
    inference(avatar_component_clause,[],[f918])).

fof(f1639,plain,
    ( spl8_62
    | ~ spl8_53
    | ~ spl8_54
    | ~ spl8_55 ),
    inference(avatar_split_clause,[],[f1638,f982,f967,f952,f1084])).

fof(f952,plain,
    ( spl8_53
  <=> v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f967,plain,
    ( spl8_54
  <=> v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f982,plain,
    ( spl8_55
  <=> m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f1638,plain,
    ( r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ spl8_53
    | ~ spl8_54
    | ~ spl8_55 ),
    inference(subsumption_resolution,[],[f1637,f954])).

fof(f954,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f952])).

fof(f1637,plain,
    ( r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ spl8_54
    | ~ spl8_55 ),
    inference(subsumption_resolution,[],[f1626,f969])).

fof(f969,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f967])).

fof(f1626,plain,
    ( r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ spl8_55 ),
    inference(resolution,[],[f984,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f984,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f982])).

fof(f1622,plain,
    ( spl8_55
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f1621,f1244,f1240,f1236,f982])).

fof(f1236,plain,
    ( spl8_65
  <=> v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f1240,plain,
    ( spl8_66
  <=> v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f1244,plain,
    ( spl8_67
  <=> m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f1621,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1620,f48])).

fof(f1620,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1619,f49])).

fof(f1619,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1618,f50])).

fof(f1618,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1617,f51])).

fof(f1617,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1616,f52])).

fof(f1616,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1615,f53])).

fof(f1615,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1614,f54])).

fof(f1614,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1613,f55])).

fof(f55,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f1613,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1612,f1237])).

fof(f1237,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f1612,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_66
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1611,f1241])).

fof(f1241,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f1611,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f1602,f1245])).

fof(f1245,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f1244])).

fof(f1602,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_67 ),
    inference(superposition,[],[f1245,f313])).

fof(f313,plain,(
    ! [X6,X4,X8,X7,X5,X3] :
      ( k8_funct_2(X3,X4,X5,X6,X7) = k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8))
      | ~ m1_subset_1(k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8)),k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
      | ~ v1_funct_2(k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8)),X3,X5)
      | ~ v1_funct_1(k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8)))
      | ~ r1_tarski(k2_relset_1(X3,X4,X6),k1_relset_1(X4,X5,k2_partfun1(X4,X5,X7,X8)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X6,X3,X4)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f309,f75])).

fof(f309,plain,(
    ! [X6,X4,X8,X7,X5,X3] :
      ( k8_funct_2(X3,X4,X5,X6,X7) = k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8))
      | ~ m1_subset_1(k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8)),k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
      | ~ v1_funct_2(k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8)),X3,X5)
      | ~ v1_funct_1(k8_funct_2(X3,X4,X5,X6,k2_partfun1(X4,X5,X7,X8)))
      | ~ sP0(X5,X3,X7,X6,X4)
      | ~ r1_tarski(k2_relset_1(X3,X4,X6),k1_relset_1(X4,X5,k2_partfun1(X4,X5,X7,X8)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X6,X3,X4)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f229,f58])).

fof(f1544,plain,
    ( ~ spl8_14
    | spl8_67 ),
    inference(avatar_contradiction_clause,[],[f1543])).

fof(f1543,plain,
    ( $false
    | ~ spl8_14
    | spl8_67 ),
    inference(subsumption_resolution,[],[f1540,f323])).

fof(f323,plain,
    ( sP0(sK3,sK1,k2_partfun1(sK2,sK3,sK7,sK4),sK6,sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl8_14
  <=> sP0(sK3,sK1,k2_partfun1(sK2,sK3,sK7,sK4),sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f1540,plain,
    ( ~ sP0(sK3,sK1,k2_partfun1(sK2,sK3,sK7,sK4),sK6,sK2)
    | spl8_67 ),
    inference(resolution,[],[f1246,f74])).

fof(f1246,plain,
    ( ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl8_67 ),
    inference(avatar_component_clause,[],[f1244])).

fof(f1527,plain,
    ( ~ spl8_67
    | spl8_54
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1526,f1240,f1236,f967,f1244])).

fof(f1526,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1525,f48])).

fof(f1525,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1524,f49])).

fof(f1524,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1523,f50])).

fof(f1523,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1522,f51])).

fof(f1522,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1521,f52])).

fof(f1521,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1520,f53])).

fof(f1520,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1519,f54])).

fof(f1519,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1518,f55])).

fof(f1518,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1517,f1237])).

fof(f1517,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f1516,f1241])).

fof(f1516,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,sK7),sK1,sK3)
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_66 ),
    inference(superposition,[],[f1241,f313])).

fof(f1505,plain,
    ( ~ spl8_14
    | spl8_66 ),
    inference(avatar_contradiction_clause,[],[f1504])).

fof(f1504,plain,
    ( $false
    | ~ spl8_14
    | spl8_66 ),
    inference(subsumption_resolution,[],[f1501,f323])).

fof(f1501,plain,
    ( ~ sP0(sK3,sK1,k2_partfun1(sK2,sK3,sK7,sK4),sK6,sK2)
    | spl8_66 ),
    inference(resolution,[],[f1242,f73])).

fof(f1242,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | spl8_66 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f1484,plain,
    ( ~ spl8_66
    | ~ spl8_67
    | spl8_53
    | ~ spl8_65 ),
    inference(avatar_split_clause,[],[f1483,f1236,f952,f1244,f1240])).

fof(f1483,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1482,f48])).

fof(f1482,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1481,f49])).

fof(f1481,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1480,f50])).

fof(f1480,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1479,f51])).

fof(f1479,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1478,f52])).

fof(f1478,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1477,f53])).

fof(f1477,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1476,f54])).

fof(f1476,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1475,f55])).

fof(f1475,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f1474,f1237])).

fof(f1474,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_65 ),
    inference(superposition,[],[f1237,f313])).

fof(f1468,plain,
    ( ~ spl8_14
    | spl8_65 ),
    inference(avatar_contradiction_clause,[],[f1467])).

fof(f1467,plain,
    ( $false
    | ~ spl8_14
    | spl8_65 ),
    inference(subsumption_resolution,[],[f1464,f323])).

fof(f1464,plain,
    ( ~ sP0(sK3,sK1,k2_partfun1(sK2,sK3,sK7,sK4),sK6,sK2)
    | spl8_65 ),
    inference(resolution,[],[f1238,f72])).

fof(f1238,plain,
    ( ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | spl8_65 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f1265,plain,
    ( ~ spl8_65
    | ~ spl8_66
    | ~ spl8_67
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f1264,f890,f1244,f1240,f1236])).

fof(f1264,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4))) ),
    inference(subsumption_resolution,[],[f1263,f48])).

fof(f1263,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1262,f49])).

fof(f1262,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1261,f50])).

fof(f1261,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1260,f51])).

fof(f1260,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1259,f52])).

fof(f1259,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1258,f53])).

fof(f1258,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1257,f54])).

fof(f1257,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f1194,f55])).

fof(f1194,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,sK7),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),sK1,sK3)
    | ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k2_partfun1(sK2,sK3,sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f109,f313])).

fof(f109,plain,(
    ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5))) ),
    inference(subsumption_resolution,[],[f108,f53])).

fof(f108,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f97,f54])).

fof(f97,plain,
    ( ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f57,f69])).

fof(f57,plain,(
    ~ r2_funct_2(sK1,sK3,k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK4)),k8_funct_2(sK1,sK2,sK3,sK6,k2_partfun1(sK2,sK3,sK7,sK5))) ),
    inference(cnf_transformation,[],[f44])).

fof(f540,plain,(
    spl8_26 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | spl8_26 ),
    inference(subsumption_resolution,[],[f538,f53])).

fof(f538,plain,
    ( ~ v1_funct_1(sK7)
    | spl8_26 ),
    inference(subsumption_resolution,[],[f537,f54])).

fof(f537,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_26 ),
    inference(resolution,[],[f522,f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f71,f69])).

fof(f522,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f520])).

fof(f456,plain,(
    spl8_23 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl8_23 ),
    inference(subsumption_resolution,[],[f454,f53])).

fof(f454,plain,
    ( ~ v1_funct_1(sK7)
    | spl8_23 ),
    inference(subsumption_resolution,[],[f453,f54])).

fof(f453,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_23 ),
    inference(resolution,[],[f450,f156])).

fof(f450,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_23 ),
    inference(subsumption_resolution,[],[f449,f50])).

fof(f449,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK6)
    | spl8_23 ),
    inference(subsumption_resolution,[],[f448,f51])).

fof(f448,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_23 ),
    inference(subsumption_resolution,[],[f447,f52])).

fof(f447,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_23 ),
    inference(subsumption_resolution,[],[f446,f132])).

fof(f132,plain,(
    ! [X1] : v1_funct_1(k7_relat_1(sK7,X1)) ),
    inference(subsumption_resolution,[],[f129,f53])).

fof(f129,plain,(
    ! [X1] :
      ( v1_funct_1(k7_relat_1(sK7,X1))
      | ~ v1_funct_1(sK7) ) ),
    inference(resolution,[],[f99,f54])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k7_relat_1(X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k7_relat_1(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f70,f69])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f446,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k7_relat_1(sK7,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_23 ),
    inference(resolution,[],[f445,f75])).

fof(f445,plain,
    ( ~ sP0(sK3,sK1,k7_relat_1(sK7,sK5),sK6,sK2)
    | spl8_23 ),
    inference(resolution,[],[f362,f74])).

fof(f362,plain,
    ( ~ m1_subset_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f360])).

fof(f437,plain,(
    spl8_22 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | spl8_22 ),
    inference(subsumption_resolution,[],[f435,f53])).

fof(f435,plain,
    ( ~ v1_funct_1(sK7)
    | spl8_22 ),
    inference(subsumption_resolution,[],[f434,f54])).

fof(f434,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_22 ),
    inference(resolution,[],[f431,f156])).

fof(f431,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_22 ),
    inference(subsumption_resolution,[],[f430,f50])).

fof(f430,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK6)
    | spl8_22 ),
    inference(subsumption_resolution,[],[f429,f51])).

fof(f429,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_22 ),
    inference(subsumption_resolution,[],[f428,f52])).

fof(f428,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_22 ),
    inference(subsumption_resolution,[],[f427,f132])).

fof(f427,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k7_relat_1(sK7,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_22 ),
    inference(resolution,[],[f426,f75])).

fof(f426,plain,
    ( ~ sP0(sK3,sK1,k7_relat_1(sK7,sK5),sK6,sK2)
    | spl8_22 ),
    inference(resolution,[],[f358,f73])).

fof(f358,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)),sK1,sK3)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f356])).

fof(f409,plain,(
    spl8_21 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | spl8_21 ),
    inference(subsumption_resolution,[],[f407,f53])).

fof(f407,plain,
    ( ~ v1_funct_1(sK7)
    | spl8_21 ),
    inference(subsumption_resolution,[],[f406,f54])).

fof(f406,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_21 ),
    inference(resolution,[],[f405,f156])).

fof(f405,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_21 ),
    inference(subsumption_resolution,[],[f404,f50])).

fof(f404,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK6)
    | spl8_21 ),
    inference(subsumption_resolution,[],[f403,f51])).

fof(f403,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_21 ),
    inference(subsumption_resolution,[],[f402,f52])).

fof(f402,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_21 ),
    inference(subsumption_resolution,[],[f401,f132])).

fof(f401,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k7_relat_1(sK7,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_21 ),
    inference(resolution,[],[f400,f75])).

fof(f400,plain,
    ( ~ sP0(sK3,sK1,k7_relat_1(sK7,sK5),sK6,sK2)
    | spl8_21 ),
    inference(resolution,[],[f354,f72])).

fof(f354,plain,
    ( ~ v1_funct_1(k8_funct_2(sK1,sK2,sK3,sK6,k7_relat_1(sK7,sK5)))
    | spl8_21 ),
    inference(avatar_component_clause,[],[f352])).

fof(f395,plain,
    ( ~ spl8_1
    | ~ spl8_8
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_8
    | spl8_14 ),
    inference(subsumption_resolution,[],[f393,f50])).

fof(f393,plain,
    ( ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_8
    | spl8_14 ),
    inference(subsumption_resolution,[],[f392,f51])).

fof(f392,plain,
    ( ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_8
    | spl8_14 ),
    inference(subsumption_resolution,[],[f391,f52])).

fof(f391,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_8
    | spl8_14 ),
    inference(subsumption_resolution,[],[f390,f177])).

fof(f177,plain,
    ( v1_funct_1(k2_partfun1(sK2,sK3,sK7,sK4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_8
  <=> v1_funct_1(k2_partfun1(sK2,sK3,sK7,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f390,plain,
    ( ~ v1_funct_1(k2_partfun1(sK2,sK3,sK7,sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | spl8_14 ),
    inference(subsumption_resolution,[],[f388,f83])).

fof(f388,plain,
    ( ~ m1_subset_1(k2_partfun1(sK2,sK3,sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK2,sK3,sK7,sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK6,sK1,sK2)
    | ~ v1_funct_1(sK6)
    | spl8_14 ),
    inference(resolution,[],[f324,f75])).

fof(f324,plain,
    ( ~ sP0(sK3,sK1,k2_partfun1(sK2,sK3,sK7,sK4),sK6,sK2)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f322])).

fof(f215,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f213,f53])).

fof(f213,plain,
    ( ~ v1_funct_1(sK7)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f212,f54])).

fof(f212,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f208,f132])).

fof(f208,plain,
    ( ~ v1_funct_1(k7_relat_1(sK7,sK4))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_8 ),
    inference(superposition,[],[f178,f69])).

fof(f178,plain,
    ( ~ v1_funct_1(k2_partfun1(sK2,sK3,sK7,sK4))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f203,plain,
    ( ~ spl8_3
    | spl8_12 ),
    inference(avatar_split_clause,[],[f122,f200,f112])).

fof(f112,plain,
    ( spl8_3
  <=> m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f122,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relat_1(k7_relat_1(sK7,sK4)))
    | ~ m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(superposition,[],[f107,f63])).

fof(f107,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK4))) ),
    inference(subsumption_resolution,[],[f106,f53])).

fof(f106,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK4)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f96,f54])).

fof(f96,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK6),k1_relset_1(sK2,sK3,k7_relat_1(sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f55,f69])).

fof(f198,plain,
    ( spl8_3
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f197,f82,f112])).

fof(f197,plain,
    ( m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f196,f53])).

fof(f196,plain,
    ( m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f174,f54])).

fof(f174,plain,
    ( m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(superposition,[],[f83,f69])).

fof(f159,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f157,f53])).

fof(f157,plain,
    ( ~ v1_funct_1(sK7)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f151,f54])).

fof(f151,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK7)
    | spl8_1 ),
    inference(resolution,[],[f71,f84])).

fof(f84,plain,
    ( ~ m1_subset_1(k2_partfun1(sK2,sK3,sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f82])).

%------------------------------------------------------------------------------

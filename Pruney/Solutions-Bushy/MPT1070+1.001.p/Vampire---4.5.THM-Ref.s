%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1070+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:12 EST 2020

% Result     : Theorem 7.41s
% Output     : Refutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  286 (1362 expanded)
%              Number of leaves         :   39 ( 565 expanded)
%              Depth                    :   21
%              Number of atoms          : 1197 (12933 expanded)
%              Number of equality atoms :   74 ( 187 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3637,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f245,f273,f1054,f1065,f1127,f1471,f1563,f1649,f1657,f1954,f2417,f2421,f2437,f2676,f2794,f2898,f3573,f3597,f3630])).

fof(f3630,plain,
    ( ~ spl7_98
    | ~ spl7_108 ),
    inference(avatar_contradiction_clause,[],[f3627])).

fof(f3627,plain,
    ( $false
    | ~ spl7_98
    | ~ spl7_108 ),
    inference(subsumption_resolution,[],[f2731,f3572])).

fof(f3572,plain,
    ( ! [X23] : ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X23,sK1)))
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f3571])).

fof(f3571,plain,
    ( spl7_108
  <=> ! [X23] : ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X23,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f2731,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f2730])).

fof(f2730,plain,
    ( spl7_98
  <=> m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f3597,plain,
    ( ~ spl7_36
    | ~ spl7_98
    | spl7_100 ),
    inference(avatar_contradiction_clause,[],[f3596])).

fof(f3596,plain,
    ( $false
    | ~ spl7_36
    | ~ spl7_98
    | spl7_100 ),
    inference(subsumption_resolution,[],[f3595,f531])).

fof(f531,plain,(
    v1_funct_1(k5_relat_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f524,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK6,sK2,sK2)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f19,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                    & v1_funct_2(X5,X1,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,X3,X4)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,X3),X4))
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
                  & v1_funct_2(X5,sK2,sK2)
                  & v1_funct_1(X5) )
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
                ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,X3,X4)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,X3),X4))
                & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
                & v1_funct_2(X5,sK2,sK2)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X3,sK2,sK3)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,sK4,X4)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,sK4),X4))
              & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
              & v1_funct_2(X5,sK2,sK2)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,sK4,X4)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,sK4),X4))
            & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
            & v1_funct_2(X5,sK2,sK2)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,sK4),sK5))
          & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X5,sK2,sK2)
          & v1_funct_1(X5) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X5] :
        ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,sK4),sK5))
        & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X5,sK2,sK2)
        & v1_funct_1(X5) )
   => ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
      & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK6,sK2,sK2)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                  & v1_funct_2(X5,X1,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                  & v1_funct_2(X5,X1,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                    ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                      & v1_funct_2(X5,X1,X1)
                      & v1_funct_1(X5) )
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                  ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                    & v1_funct_2(X5,X1,X1)
                    & v1_funct_1(X5) )
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_funct_2)).

fof(f524,plain,
    ( v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f499,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f499,plain,(
    ! [X24,X23,X25] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_funct_1(k5_relat_1(X23,sK5))
      | ~ v1_funct_1(X23) ) ),
    inference(subsumption_resolution,[],[f492,f55])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f492,plain,(
    ! [X24,X23,X25] :
      ( v1_funct_1(k5_relat_1(X23,sK5))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ v1_funct_1(X23) ) ),
    inference(resolution,[],[f209,f56])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f209,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f82,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f3595,plain,
    ( ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl7_36
    | ~ spl7_98
    | spl7_100 ),
    inference(subsumption_resolution,[],[f3594,f1064])).

fof(f1064,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f1062])).

fof(f1062,plain,
    ( spl7_36
  <=> v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f3594,plain,
    ( ~ v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl7_98
    | spl7_100 ),
    inference(subsumption_resolution,[],[f3593,f2731])).

fof(f3593,plain,
    ( ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | spl7_100 ),
    inference(subsumption_resolution,[],[f3592,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f3592,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | spl7_100 ),
    inference(subsumption_resolution,[],[f3591,f58])).

fof(f58,plain,(
    v1_funct_2(sK6,sK2,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f3591,plain,
    ( ~ v1_funct_2(sK6,sK2,sK2)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | spl7_100 ),
    inference(subsumption_resolution,[],[f3589,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3589,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK6,sK2,sK2)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | spl7_100 ),
    inference(resolution,[],[f2793,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
        & v1_funct_1(k5_relat_1(X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
        & v1_funct_1(k5_relat_1(X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X3,X0,X0)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
        & v1_funct_1(k5_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_2)).

fof(f2793,plain,
    ( ~ v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | spl7_100 ),
    inference(avatar_component_clause,[],[f2791])).

fof(f2791,plain,
    ( spl7_100
  <=> v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f3573,plain,
    ( spl7_108
    | spl7_70
    | spl7_99 ),
    inference(avatar_split_clause,[],[f3569,f2787,f1644,f3571])).

fof(f1644,plain,
    ( spl7_70
  <=> ! [X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f2787,plain,
    ( spl7_99
  <=> r1_tarski(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f3569,plain,
    ( ! [X23,X22] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X22)))
        | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X23,sK1))) )
    | spl7_99 ),
    inference(subsumption_resolution,[],[f3568,f57])).

fof(f3568,plain,
    ( ! [X23,X22] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X22)))
        | ~ v1_funct_1(sK6)
        | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X23,sK1))) )
    | spl7_99 ),
    inference(subsumption_resolution,[],[f3530,f531])).

fof(f3530,plain,
    ( ! [X23,X22] :
        ( ~ v1_funct_1(k5_relat_1(sK4,sK5))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X22)))
        | ~ v1_funct_1(sK6)
        | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X23,sK1))) )
    | spl7_99 ),
    inference(resolution,[],[f577,f2789])).

fof(f2789,plain,
    ( ~ r1_tarski(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k2_zfmisc_1(sK2,sK1))
    | spl7_99 ),
    inference(avatar_component_clause,[],[f2787])).

fof(f577,plain,(
    ! [X70,X68,X66,X71,X69,X67] :
      ( r1_tarski(k5_relat_1(X69,X66),k2_zfmisc_1(X70,X68))
      | ~ v1_funct_1(X66)
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | ~ v1_funct_1(X69)
      | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X67,X68))) ) ),
    inference(resolution,[],[f285,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f285,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f83,f81])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2898,plain,
    ( ~ spl7_35
    | spl7_98 ),
    inference(avatar_contradiction_clause,[],[f2897])).

fof(f2897,plain,
    ( $false
    | ~ spl7_35
    | spl7_98 ),
    inference(subsumption_resolution,[],[f2887,f1053])).

fof(f1053,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1051,plain,
    ( spl7_35
  <=> r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f2887,plain,
    ( ~ r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | spl7_98 ),
    inference(resolution,[],[f2732,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2732,plain,
    ( ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl7_98 ),
    inference(avatar_component_clause,[],[f2730])).

fof(f2794,plain,
    ( ~ spl7_99
    | ~ spl7_100
    | spl7_16
    | spl7_29
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f2785,f1124,f988,f926,f2791,f2787])).

fof(f926,plain,
    ( spl7_16
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f988,plain,
    ( spl7_29
  <=> r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f1124,plain,
    ( spl7_42
  <=> v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f2785,plain,
    ( ~ v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ r1_tarski(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k2_zfmisc_1(sK2,sK1))
    | spl7_16
    | spl7_29
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f2784,f1126])).

fof(f1126,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f2784,plain,
    ( ~ v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ r1_tarski(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k2_zfmisc_1(sK2,sK1))
    | spl7_16
    | spl7_29 ),
    inference(resolution,[],[f2783,f167])).

fof(f167,plain,(
    ! [X6,X7,X5] :
      ( r2_funct_2(X5,X6,X7,X7)
      | ~ v1_funct_2(X7,X5,X6)
      | ~ v1_funct_1(X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X5,X6)) ) ),
    inference(resolution,[],[f85,f67])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f2783,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | spl7_16
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2782,f93])).

fof(f93,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f68,f59])).

fof(f68,plain,(
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

fof(f2782,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK6)
    | spl7_16
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2781,f91])).

fof(f91,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f68,f54])).

fof(f2781,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | spl7_16
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2780,f92])).

fof(f92,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f68,f56])).

fof(f2780,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | spl7_16
    | spl7_29 ),
    inference(superposition,[],[f2776,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f2776,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | spl7_16
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2775,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f2775,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_16
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2774,f60])).

fof(f60,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f2774,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_16
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2773,f927])).

fof(f927,plain,
    ( k1_xboole_0 != sK3
    | spl7_16 ),
    inference(avatar_component_clause,[],[f926])).

fof(f2773,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2772,f52])).

fof(f2772,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2771,f54])).

fof(f2771,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2770,f55])).

fof(f2770,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_29 ),
    inference(subsumption_resolution,[],[f2768,f56])).

fof(f2768,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_29 ),
    inference(superposition,[],[f990,f361])).

fof(f361,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( k5_relat_1(X8,X9) = k8_funct_2(X5,X6,X7,X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X8)
      | k1_xboole_0 = X6
      | ~ r1_tarski(k2_relset_1(X5,X6,X8),k1_relset_1(X6,X7,X9))
      | ~ v1_funct_2(X8,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( k5_relat_1(X8,X9) = k8_funct_2(X5,X6,X7,X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X8)
      | k1_xboole_0 = X6
      | ~ r1_tarski(k2_relset_1(X5,X6,X8),k1_relset_1(X6,X7,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X8,X5,X6)
      | ~ v1_funct_1(X8) ) ),
    inference(superposition,[],[f81,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(f990,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | spl7_29 ),
    inference(avatar_component_clause,[],[f988])).

fof(f2676,plain,
    ( ~ spl7_29
    | ~ spl7_3
    | ~ spl7_4
    | spl7_30 ),
    inference(avatar_split_clause,[],[f2675,f996,f217,f213,f988])).

fof(f213,plain,
    ( spl7_3
  <=> v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f217,plain,
    ( spl7_4
  <=> m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f996,plain,
    ( spl7_30
  <=> r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f2675,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_30 ),
    inference(subsumption_resolution,[],[f2674,f57])).

fof(f2674,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK6)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_30 ),
    inference(subsumption_resolution,[],[f2673,f59])).

fof(f2673,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_30 ),
    inference(subsumption_resolution,[],[f2672,f214])).

fof(f214,plain,
    ( v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f213])).

fof(f2672,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl7_4
    | spl7_30 ),
    inference(subsumption_resolution,[],[f2662,f218])).

fof(f218,plain,
    ( m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f2662,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | spl7_30 ),
    inference(superposition,[],[f998,f81])).

fof(f998,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f996])).

fof(f2437,plain,(
    ~ spl7_71 ),
    inference(avatar_contradiction_clause,[],[f2435])).

fof(f2435,plain,
    ( $false
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f54,f1648])).

fof(f1648,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f1647,plain,
    ( spl7_71
  <=> ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f2421,plain,(
    ~ spl7_70 ),
    inference(avatar_contradiction_clause,[],[f2419])).

fof(f2419,plain,
    ( $false
    | ~ spl7_70 ),
    inference(subsumption_resolution,[],[f59,f1645])).

fof(f1645,plain,
    ( ! [X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f2417,plain,
    ( ~ spl7_27
    | ~ spl7_28
    | ~ spl7_30
    | spl7_16
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f2416,f976,f926,f996,f984,f980])).

fof(f980,plain,
    ( spl7_27
  <=> r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f984,plain,
    ( spl7_28
  <=> m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f976,plain,
    ( spl7_26
  <=> v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f2416,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | spl7_16
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f2415,f977])).

fof(f977,plain,
    ( v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f976])).

fof(f2415,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | spl7_16 ),
    inference(subsumption_resolution,[],[f2414,f927])).

fof(f2414,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f1891,f301])).

fof(f301,plain,(
    v1_funct_1(k5_relat_1(sK6,sK4)) ),
    inference(subsumption_resolution,[],[f300,f52])).

fof(f300,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f292,f53])).

fof(f292,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK4))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f265,f54])).

fof(f265,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | v1_funct_1(k5_relat_1(sK6,X6))
      | ~ v1_funct_2(X6,sK2,X7)
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f264,f57])).

fof(f264,plain,(
    ! [X6,X7] :
      ( v1_funct_1(k5_relat_1(sK6,X6))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | ~ v1_funct_2(X6,sK2,X7)
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f260,f58])).

fof(f260,plain,(
    ! [X6,X7] :
      ( v1_funct_1(k5_relat_1(sK6,X6))
      | ~ v1_funct_2(sK6,sK2,sK2)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | ~ v1_funct_2(X6,sK2,X7)
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f72,f59])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k5_relat_1(X3,X2))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1891,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f1890,f55])).

fof(f1890,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f1877,f56])).

fof(f1877,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3) ),
    inference(superposition,[],[f228,f361])).

fof(f228,plain,(
    ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5)) ),
    inference(subsumption_resolution,[],[f227,f57])).

fof(f227,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f226,f59])).

fof(f226,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f225,f52])).

fof(f225,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f207,f54])).

fof(f207,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f61,f81])).

fof(f61,plain,(
    ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1954,plain,
    ( spl7_27
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f1953])).

fof(f1953,plain,
    ( $false
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f1952,f93])).

fof(f1952,plain,
    ( ~ v1_relat_1(sK6)
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f1951,f91])).

fof(f1951,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f1949,f128])).

fof(f128,plain,(
    r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(superposition,[],[f120,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f120,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f119,f56])).

fof(f119,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(superposition,[],[f60,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1949,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | spl7_27
    | ~ spl7_28 ),
    inference(resolution,[],[f1916,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1916,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK5)) )
    | spl7_27
    | ~ spl7_28 ),
    inference(resolution,[],[f1915,f71])).

fof(f71,plain,(
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

fof(f1915,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relat_1(sK5))
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f1914,f985])).

fof(f985,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f984])).

fof(f1914,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relat_1(sK5))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl7_27 ),
    inference(superposition,[],[f1912,f70])).

fof(f1912,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relat_1(sK5))
    | spl7_27 ),
    inference(subsumption_resolution,[],[f1910,f56])).

fof(f1910,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relat_1(sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | spl7_27 ),
    inference(superposition,[],[f982,f69])).

fof(f982,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f980])).

fof(f1657,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f1656])).

fof(f1656,plain,
    ( $false
    | spl7_26 ),
    inference(subsumption_resolution,[],[f1655,f52])).

fof(f1655,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_26 ),
    inference(subsumption_resolution,[],[f1654,f53])).

fof(f1654,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_26 ),
    inference(subsumption_resolution,[],[f1653,f54])).

fof(f1653,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_26 ),
    inference(subsumption_resolution,[],[f1652,f57])).

fof(f1652,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_26 ),
    inference(subsumption_resolution,[],[f1651,f58])).

fof(f1651,plain,
    ( ~ v1_funct_2(sK6,sK2,sK2)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_26 ),
    inference(subsumption_resolution,[],[f1650,f59])).

fof(f1650,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK6,sK2,sK2)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_26 ),
    inference(resolution,[],[f978,f73])).

fof(f978,plain,
    ( ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f976])).

fof(f1649,plain,
    ( spl7_70
    | spl7_71
    | spl7_28 ),
    inference(avatar_split_clause,[],[f1642,f984,f1647,f1644])).

fof(f1642,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | spl7_28 ),
    inference(subsumption_resolution,[],[f1641,f57])).

fof(f1641,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK6) )
    | spl7_28 ),
    inference(subsumption_resolution,[],[f1639,f52])).

fof(f1639,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK6) )
    | spl7_28 ),
    inference(resolution,[],[f986,f285])).

fof(f986,plain,
    ( ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl7_28 ),
    inference(avatar_component_clause,[],[f984])).

fof(f1563,plain,
    ( spl7_3
    | spl7_16 ),
    inference(avatar_split_clause,[],[f1562,f926,f213])).

fof(f1562,plain,
    ( v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | spl7_16 ),
    inference(subsumption_resolution,[],[f1561,f53])).

fof(f1561,plain,
    ( v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | spl7_16 ),
    inference(subsumption_resolution,[],[f1560,f927])).

fof(f1560,plain,
    ( k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1559,f52])).

fof(f1559,plain,
    ( ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1558,f54])).

fof(f1558,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1557,f55])).

fof(f1557,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1554,f56])).

fof(f1554,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(resolution,[],[f60,f360])).

fof(f360,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ r1_tarski(k2_relset_1(X10,X11,X13),k1_relset_1(X11,X12,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X13)
      | k1_xboole_0 = X11
      | v1_funct_1(k8_funct_2(X10,X11,X12,X13,X14))
      | ~ v1_funct_2(X13,X10,X11) ) ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( v1_funct_1(k8_funct_2(X10,X11,X12,X13,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X13)
      | k1_xboole_0 = X11
      | ~ r1_tarski(k2_relset_1(X10,X11,X13),k1_relset_1(X11,X12,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_2(X13,X10,X11)
      | ~ v1_funct_1(X13) ) ),
    inference(superposition,[],[f82,f76])).

fof(f1471,plain,(
    ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1470])).

fof(f1470,plain,
    ( $false
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f62,f1469])).

fof(f1469,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl7_16 ),
    inference(duplicate_literal_removal,[],[f1468])).

fof(f1468,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_16 ),
    inference(superposition,[],[f1399,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f1399,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f51,f928])).

fof(f928,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f926])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f1127,plain,
    ( spl7_16
    | spl7_42
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f1122,f251,f217,f213,f1124,f926])).

fof(f251,plain,
    ( spl7_6
  <=> v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1122,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | k1_xboole_0 = sK3
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1121,f53])).

fof(f1121,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1120,f60])).

fof(f1120,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1119,f52])).

fof(f1119,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1118,f54])).

fof(f1118,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1117,f55])).

fof(f1117,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f874,f56])).

fof(f874,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(superposition,[],[f296,f361])).

fof(f296,plain,
    ( v1_funct_1(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f295,f214])).

fof(f295,plain,
    ( v1_funct_1(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f289,f252])).

fof(f252,plain,
    ( v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f251])).

fof(f289,plain,
    ( v1_funct_1(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)))
    | ~ v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl7_4 ),
    inference(resolution,[],[f265,f218])).

fof(f1065,plain,
    ( spl7_16
    | spl7_36
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f1060,f251,f1062,f926])).

fof(f1060,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | k1_xboole_0 = sK3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1059,f53])).

fof(f1059,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1058,f60])).

fof(f1058,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1057,f52])).

fof(f1057,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1056,f54])).

fof(f1056,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1055,f55])).

fof(f1055,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f868,f56])).

fof(f868,plain,
    ( v1_funct_2(k5_relat_1(sK4,sK5),sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_6 ),
    inference(superposition,[],[f252,f361])).

fof(f1054,plain,
    ( spl7_16
    | spl7_35
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1049,f217,f1051,f926])).

fof(f1049,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1048,f53])).

fof(f1048,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1047,f60])).

fof(f1047,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1046,f52])).

fof(f1046,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1045,f54])).

fof(f1045,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1044,f55])).

fof(f1044,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f867,f56])).

fof(f867,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl7_4 ),
    inference(superposition,[],[f248,f361])).

fof(f248,plain,
    ( r1_tarski(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k2_zfmisc_1(sK2,sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f218,f66])).

fof(f273,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f271,f52])).

fof(f271,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f270,f53])).

fof(f270,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f269,f54])).

fof(f269,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f268,f55])).

fof(f268,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f267,f56])).

fof(f267,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_6 ),
    inference(resolution,[],[f266,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP0(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ sP0(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f266,plain,
    ( ~ sP0(sK1,sK2,sK5,sK4,sK3)
    | spl7_6 ),
    inference(resolution,[],[f253,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X1,X4,X0,X3,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X1,X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k8_funct_2(X1,X4,X0,X3,X2),X1,X0)
        & v1_funct_1(k8_funct_2(X1,X4,X0,X3,X2)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ sP0(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f253,plain,
    ( ~ v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f251])).

fof(f245,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f243,f52])).

fof(f243,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f242,f53])).

fof(f242,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f241,f54])).

fof(f241,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f240,f55])).

fof(f240,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f239,f56])).

fof(f239,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl7_4 ),
    inference(resolution,[],[f237,f80])).

fof(f237,plain,
    ( ~ sP0(sK1,sK2,sK5,sK4,sK3)
    | spl7_4 ),
    inference(resolution,[],[f219,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X1,X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f219,plain,
    ( ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f217])).

%------------------------------------------------------------------------------

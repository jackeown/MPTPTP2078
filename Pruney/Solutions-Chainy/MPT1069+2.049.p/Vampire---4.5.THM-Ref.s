%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 460 expanded)
%              Number of leaves         :   24 ( 188 expanded)
%              Depth                    :   20
%              Number of atoms          :  546 (3870 expanded)
%              Number of equality atoms :  133 ( 921 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f740,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f269,f651,f654,f720])).

fof(f720,plain,(
    ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f684,f78])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f684,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_19 ),
    inference(superposition,[],[f68,f268])).

fof(f268,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl7_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f68,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f55,f54,f53,f52])).

fof(f52,plain,
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
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f654,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f652,f76])).

fof(f76,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f652,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_6 ),
    inference(resolution,[],[f162,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f162,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl7_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f651,plain,
    ( ~ spl7_5
    | ~ spl7_18
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_18
    | spl7_19 ),
    inference(subsumption_resolution,[],[f649,f600])).

fof(f600,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl7_5
    | spl7_19 ),
    inference(subsumption_resolution,[],[f599,f69])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f599,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ spl7_5
    | spl7_19 ),
    inference(subsumption_resolution,[],[f598,f70])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f598,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl7_5
    | spl7_19 ),
    inference(subsumption_resolution,[],[f596,f267])).

fof(f267,plain,
    ( k1_xboole_0 != sK2
    | spl7_19 ),
    inference(avatar_component_clause,[],[f266])).

fof(f596,plain,
    ( k1_xboole_0 = sK2
    | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f518,f71])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f518,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
        | k1_xboole_0 = X3
        | k1_funct_1(k5_relat_1(X2,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X2,sK5))
        | ~ v1_funct_2(X2,sK1,X3)
        | ~ v1_funct_1(X2) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f516,f132])).

fof(f132,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f130,f86])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f130,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(resolution,[],[f80,f73])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f516,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k5_relat_1(X2,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X2,sK5))
        | k1_xboole_0 = X3
        | ~ v1_relat_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
        | ~ v1_funct_2(X2,sK1,X3)
        | ~ v1_funct_1(X2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f319,f72])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f319,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k1_funct_1(k5_relat_1(X1,X2),sK5) = k1_funct_1(X2,k1_funct_1(X1,sK5))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl7_5 ),
    inference(resolution,[],[f158,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

fof(f158,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_5
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f649,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl7_5
    | ~ spl7_18
    | spl7_19 ),
    inference(superposition,[],[f540,f632])).

fof(f632,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(resolution,[],[f627,f178])).

fof(f178,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(resolution,[],[f101,f73])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f627,plain,
    ( ! [X1] :
        ( ~ v5_relat_1(sK4,X1)
        | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,sK5)) )
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f626,f132])).

fof(f626,plain,
    ( ! [X1] :
        ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,sK5))
        | ~ v5_relat_1(sK4,X1)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f621,f72])).

fof(f621,plain,
    ( ! [X1] :
        ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,sK5))
        | ~ v1_funct_1(sK4)
        | ~ v5_relat_1(sK4,X1)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(resolution,[],[f544,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f544,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(resolution,[],[f541,f462])).

fof(f462,plain,(
    v5_relat_1(sK3,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f459,f131])).

fof(f131,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f129,f86])).

fof(f129,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f80,f71])).

fof(f459,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f377,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f377,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f375,f208])).

fof(f208,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f100,f73])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f375,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(superposition,[],[f75,f202])).

fof(f202,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f99,f71])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f75,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f541,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | r2_hidden(k1_funct_1(sK3,sK5),X0) )
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(resolution,[],[f448,f158])).

fof(f448,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | r2_hidden(k1_funct_1(sK3,X6),X7)
        | ~ v5_relat_1(sK3,X7) )
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f447,f131])).

fof(f447,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | r2_hidden(k1_funct_1(sK3,X6),X7)
        | ~ v5_relat_1(sK3,X7)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f435,f69])).

fof(f435,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | r2_hidden(k1_funct_1(sK3,X6),X7)
        | ~ v1_funct_1(sK3)
        | ~ v5_relat_1(sK3,X7)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_18 ),
    inference(superposition,[],[f91,f383])).

fof(f383,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_18 ),
    inference(superposition,[],[f207,f264])).

fof(f264,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl7_18
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f207,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f100,f71])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f540,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl7_19 ),
    inference(superposition,[],[f77,f498])).

fof(f498,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | spl7_19 ),
    inference(superposition,[],[f426,f318])).

fof(f318,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f317,f69])).

fof(f317,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ v1_funct_1(sK3)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f316,f70])).

fof(f316,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f315,f71])).

fof(f315,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f314,f72])).

fof(f314,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f313,f73])).

fof(f313,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f312,f267])).

fof(f312,plain,
    ( k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f110,f75])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f426,plain,(
    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f422,f69])).

fof(f422,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f311,f71])).

fof(f311,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_partfun1(X8,X9,sK2,sK0,X10,sK4) = k5_relat_1(X10,sK4)
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f299,f72])).

fof(f299,plain,(
    ! [X10,X8,X9] :
      ( k1_partfun1(X8,X9,sK2,sK0,X10,sK4) = k5_relat_1(X10,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X10) ) ),
    inference(resolution,[],[f111,f73])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f77,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f269,plain,
    ( spl7_18
    | spl7_19 ),
    inference(avatar_split_clause,[],[f260,f266,f262])).

fof(f260,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f255,f70])).

fof(f255,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f102,f71])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f163,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f136,f160,f156])).

fof(f136,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f90,f74])).

fof(f74,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:52:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (7852)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (7853)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (7860)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (7852)Refutation not found, incomplete strategy% (7852)------------------------------
% 0.21/0.52  % (7852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7857)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (7854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (7869)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (7861)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (7863)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (7857)Refutation not found, incomplete strategy% (7857)------------------------------
% 0.21/0.53  % (7857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7857)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7857)Memory used [KB]: 10874
% 0.21/0.53  % (7857)Time elapsed: 0.115 s
% 0.21/0.53  % (7857)------------------------------
% 0.21/0.53  % (7857)------------------------------
% 0.21/0.53  % (7855)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (7871)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (7873)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (7868)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (7864)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7874)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (7876)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (7856)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (7872)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (7865)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (7866)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (7852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7852)Memory used [KB]: 10874
% 0.21/0.55  % (7852)Time elapsed: 0.104 s
% 0.21/0.55  % (7852)------------------------------
% 0.21/0.55  % (7852)------------------------------
% 0.21/0.55  % (7858)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (7867)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (7859)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (7851)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (7862)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.56  % (7875)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (7870)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (7861)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (7856)Refutation not found, incomplete strategy% (7856)------------------------------
% 0.21/0.57  % (7856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7856)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7856)Memory used [KB]: 6396
% 0.21/0.57  % (7856)Time elapsed: 0.138 s
% 0.21/0.57  % (7856)------------------------------
% 0.21/0.57  % (7856)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f740,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f163,f269,f651,f654,f720])).
% 0.21/0.57  fof(f720,plain,(
% 0.21/0.57    ~spl7_19),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f719])).
% 0.21/0.57  fof(f719,plain,(
% 0.21/0.57    $false | ~spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f684,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f684,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl7_19),
% 0.21/0.57    inference(superposition,[],[f68,f268])).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | ~spl7_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f266])).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    spl7_19 <=> k1_xboole_0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ~v1_xboole_0(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f55,f54,f53,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.57    inference(flattening,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.57    inference(negated_conjecture,[],[f22])).
% 0.21/0.57  fof(f22,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.57  fof(f654,plain,(
% 0.21/0.57    ~spl7_6),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f653])).
% 0.21/0.57  fof(f653,plain,(
% 0.21/0.57    $false | ~spl7_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f652,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f652,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~spl7_6),
% 0.21/0.57    inference(resolution,[],[f162,f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    v1_xboole_0(sK1) | ~spl7_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f160])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    spl7_6 <=> v1_xboole_0(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.57  fof(f651,plain,(
% 0.21/0.57    ~spl7_5 | ~spl7_18 | spl7_19),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f650])).
% 0.21/0.57  fof(f650,plain,(
% 0.21/0.57    $false | (~spl7_5 | ~spl7_18 | spl7_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f649,f600])).
% 0.21/0.57  fof(f600,plain,(
% 0.21/0.57    k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl7_5 | spl7_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f599,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    v1_funct_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f599,plain,(
% 0.21/0.57    k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | (~spl7_5 | spl7_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f598,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f598,plain,(
% 0.21/0.57    k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | (~spl7_5 | spl7_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f596,f267])).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    k1_xboole_0 != sK2 | spl7_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f266])).
% 0.21/0.57  fof(f596,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~spl7_5),
% 0.21/0.57    inference(resolution,[],[f518,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f518,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | k1_xboole_0 = X3 | k1_funct_1(k5_relat_1(X2,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X2,sK5)) | ~v1_funct_2(X2,sK1,X3) | ~v1_funct_1(X2)) ) | ~spl7_5),
% 0.21/0.57    inference(subsumption_resolution,[],[f516,f132])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    v1_relat_1(sK4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f130,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.21/0.57    inference(resolution,[],[f80,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.57  fof(f516,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k1_funct_1(k5_relat_1(X2,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X2,sK5)) | k1_xboole_0 = X3 | ~v1_relat_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v1_funct_2(X2,sK1,X3) | ~v1_funct_1(X2)) ) | ~spl7_5),
% 0.21/0.57    inference(resolution,[],[f319,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    v1_funct_1(sK4)),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_funct_1(k5_relat_1(X1,X2),sK5) = k1_funct_1(X2,k1_funct_1(X1,sK5)) | k1_xboole_0 = X0 | ~v1_relat_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | ~spl7_5),
% 0.21/0.57    inference(resolution,[],[f158,f109])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.57    inference(flattening,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    r2_hidden(sK5,sK1) | ~spl7_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f156])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    spl7_5 <=> r2_hidden(sK5,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.57  fof(f649,plain,(
% 0.21/0.57    k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl7_5 | ~spl7_18 | spl7_19)),
% 0.21/0.57    inference(superposition,[],[f540,f632])).
% 0.21/0.57  fof(f632,plain,(
% 0.21/0.57    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl7_5 | ~spl7_18)),
% 0.21/0.57    inference(resolution,[],[f627,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    v5_relat_1(sK4,sK0)),
% 0.21/0.57    inference(resolution,[],[f101,f73])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f627,plain,(
% 0.21/0.57    ( ! [X1] : (~v5_relat_1(sK4,X1) | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,sK5))) ) | (~spl7_5 | ~spl7_18)),
% 0.21/0.57    inference(subsumption_resolution,[],[f626,f132])).
% 0.21/0.57  fof(f626,plain,(
% 0.21/0.57    ( ! [X1] : (k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,sK5)) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) ) | (~spl7_5 | ~spl7_18)),
% 0.21/0.57    inference(subsumption_resolution,[],[f621,f72])).
% 0.21/0.57  fof(f621,plain,(
% 0.21/0.57    ( ! [X1] : (k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) ) | (~spl7_5 | ~spl7_18)),
% 0.21/0.57    inference(resolution,[],[f544,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.57  fof(f544,plain,(
% 0.21/0.57    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl7_5 | ~spl7_18)),
% 0.21/0.57    inference(resolution,[],[f541,f462])).
% 0.21/0.57  fof(f462,plain,(
% 0.21/0.57    v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f459,f131])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    v1_relat_1(sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f129,f86])).
% 0.21/0.57  fof(f129,plain,(
% 0.21/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.57    inference(resolution,[],[f80,f71])).
% 0.21/0.57  fof(f459,plain,(
% 0.21/0.57    v5_relat_1(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f377,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.57  fof(f377,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.21/0.57    inference(forward_demodulation,[],[f375,f208])).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.57    inference(resolution,[],[f100,f73])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f375,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.57    inference(superposition,[],[f75,f202])).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f99,f71])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f541,plain,(
% 0.21/0.57    ( ! [X0] : (~v5_relat_1(sK3,X0) | r2_hidden(k1_funct_1(sK3,sK5),X0)) ) | (~spl7_5 | ~spl7_18)),
% 0.21/0.57    inference(resolution,[],[f448,f158])).
% 0.21/0.57  fof(f448,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | r2_hidden(k1_funct_1(sK3,X6),X7) | ~v5_relat_1(sK3,X7)) ) | ~spl7_18),
% 0.21/0.57    inference(subsumption_resolution,[],[f447,f131])).
% 0.21/0.57  fof(f447,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | r2_hidden(k1_funct_1(sK3,X6),X7) | ~v5_relat_1(sK3,X7) | ~v1_relat_1(sK3)) ) | ~spl7_18),
% 0.21/0.57    inference(subsumption_resolution,[],[f435,f69])).
% 0.21/0.57  fof(f435,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | r2_hidden(k1_funct_1(sK3,X6),X7) | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,X7) | ~v1_relat_1(sK3)) ) | ~spl7_18),
% 0.21/0.57    inference(superposition,[],[f91,f383])).
% 0.21/0.57  fof(f383,plain,(
% 0.21/0.57    sK1 = k1_relat_1(sK3) | ~spl7_18),
% 0.21/0.57    inference(superposition,[],[f207,f264])).
% 0.21/0.57  fof(f264,plain,(
% 0.21/0.57    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl7_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f262])).
% 0.21/0.57  fof(f262,plain,(
% 0.21/0.57    spl7_18 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f100,f71])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.57  fof(f540,plain,(
% 0.21/0.57    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl7_19),
% 0.21/0.57    inference(superposition,[],[f77,f498])).
% 0.21/0.57  fof(f498,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | spl7_19),
% 0.21/0.57    inference(superposition,[],[f426,f318])).
% 0.21/0.57  fof(f318,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f317,f69])).
% 0.21/0.57  fof(f317,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~v1_funct_1(sK3) | spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f316,f70])).
% 0.21/0.57  fof(f316,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f315,f71])).
% 0.21/0.57  fof(f315,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f314,f72])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f313,f73])).
% 0.21/0.57  fof(f313,plain,(
% 0.21/0.57    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | spl7_19),
% 0.21/0.57    inference(subsumption_resolution,[],[f312,f267])).
% 0.21/0.57  fof(f312,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f110,f75])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.57    inference(flattening,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.21/0.57  fof(f426,plain,(
% 0.21/0.57    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f422,f69])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f311,f71])).
% 0.21/0.57  fof(f311,plain,(
% 0.21/0.57    ( ! [X10,X8,X9] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_partfun1(X8,X9,sK2,sK0,X10,sK4) = k5_relat_1(X10,sK4) | ~v1_funct_1(X10)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f299,f72])).
% 0.21/0.57  fof(f299,plain,(
% 0.21/0.57    ( ! [X10,X8,X9] : (k1_partfun1(X8,X9,sK2,sK0,X10,sK4) = k5_relat_1(X10,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X10)) )),
% 0.21/0.57    inference(resolution,[],[f111,f73])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    spl7_18 | spl7_19),
% 0.21/0.57    inference(avatar_split_clause,[],[f260,f266,f262])).
% 0.21/0.57  fof(f260,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f255,f70])).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.57    inference(resolution,[],[f102,f71])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    spl7_5 | spl7_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f136,f160,f156])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    v1_xboole_0(sK1) | r2_hidden(sK5,sK1)),
% 0.21/0.57    inference(resolution,[],[f90,f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    m1_subset_1(sK5,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (7861)------------------------------
% 0.21/0.57  % (7861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7861)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (7861)Memory used [KB]: 11129
% 0.21/0.57  % (7861)Time elapsed: 0.111 s
% 0.21/0.57  % (7861)------------------------------
% 0.21/0.57  % (7861)------------------------------
% 0.21/0.58  % (7850)Success in time 0.215 s
%------------------------------------------------------------------------------

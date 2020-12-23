%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  161 (4529 expanded)
%              Number of leaves         :   24 (1334 expanded)
%              Depth                    :   30
%              Number of atoms          :  560 (30217 expanded)
%              Number of equality atoms :  120 (2345 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1004,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f153,f228,f370,f519,f752,f799,f1001])).

fof(f1001,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_31 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f999,f100])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f999,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f998,f778])).

fof(f778,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f594,f765])).

fof(f765,plain,
    ( k1_xboole_0 = sK1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f754,f594])).

fof(f754,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f735,f100])).

fof(f735,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f718,f100])).

fof(f718,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(sK1,X0)
        | k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f632,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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

fof(f632,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ r1_tarski(k1_xboole_0,X3)
        | ~ r1_tarski(sK1,X2) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f631,f587])).

fof(f587,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f438,f583])).

fof(f583,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f561,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f561,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f560,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f560,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f532,f545])).

fof(f545,plain,
    ( k1_xboole_0 = sK2
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f544,f157])).

fof(f157,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl7_2 ),
    inference(backward_demodulation,[],[f117,f155])).

fof(f155,plain,(
    ! [X1] : k2_partfun1(sK0,sK3,sK4,X1) = k7_relat_1(sK4,X1) ),
    inference(subsumption_resolution,[],[f140,f60])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f46,f45])).

fof(f45,plain,
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

fof(f46,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f140,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK3,sK4,X1) = k7_relat_1(sK4,X1)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f62,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f544,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f528,f543])).

fof(f543,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f525,f438])).

fof(f525,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f522,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f522,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f120,f155])).

fof(f120,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f528,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f522,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f532,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_3 ),
    inference(resolution,[],[f522,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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

fof(f438,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl7_6 ),
    inference(resolution,[],[f406,f63])).

fof(f63,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f406,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f404,f134])).

fof(f134,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f62,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f404,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1
        | ~ v1_relat_1(sK4) )
    | ~ spl7_6 ),
    inference(superposition,[],[f69,f387])).

fof(f387,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f135,f148])).

fof(f148,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_6
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f135,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f62,f86])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f631,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_xboole_0,X3)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X2) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f618,f569])).

fof(f569,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f551,f67])).

fof(f551,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f154,f545])).

fof(f154,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f64,f139])).

fof(f139,plain,(
    ! [X0] : k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f62,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f64,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f618,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ r1_tarski(k9_relat_1(sK4,sK1),X3)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X2) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(superposition,[],[f231,f583])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k9_relat_1(sK4,X0),X1)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2) ) ),
    inference(subsumption_resolution,[],[f230,f204])).

fof(f204,plain,(
    ! [X1] : v1_relat_1(k7_relat_1(sK4,X1)) ),
    inference(resolution,[],[f160,f85])).

fof(f160,plain,(
    ! [X2] : m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(forward_demodulation,[],[f159,f155])).

fof(f159,plain,(
    ! [X2] : m1_subset_1(k2_partfun1(sK0,sK3,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(subsumption_resolution,[],[f141,f60])).

fof(f141,plain,(
    ! [X2] :
      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f62,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK4,X0),X1)
      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2)
      | ~ v1_relat_1(k7_relat_1(sK4,X0)) ) ),
    inference(superposition,[],[f84,f171])).

fof(f171,plain,(
    ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0)) ),
    inference(resolution,[],[f134,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f594,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f550,f583])).

fof(f550,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f157,f545])).

fof(f998,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_31 ),
    inference(trivial_inequality_removal,[],[f993])).

fof(f993,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_31 ),
    inference(superposition,[],[f751,f777])).

fof(f777,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f593,f765])).

fof(f593,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f546,f583])).

fof(f546,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f543,f545])).

fof(f751,plain,
    ( ! [X24] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X24,k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X24)
        | ~ r1_tarski(k1_xboole_0,X24) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f750])).

fof(f750,plain,
    ( spl7_31
  <=> ! [X24] :
        ( ~ r1_tarski(k1_xboole_0,X24)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X24)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X24,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f799,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_29 ),
    inference(avatar_contradiction_clause,[],[f798])).

fof(f798,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_29 ),
    inference(subsumption_resolution,[],[f792,f100])).

fof(f792,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_29 ),
    inference(backward_demodulation,[],[f744,f765])).

fof(f744,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl7_29
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f752,plain,
    ( ~ spl7_29
    | spl7_31
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f730,f146,f119,f115,f750,f742])).

fof(f730,plain,
    ( ! [X24] :
        ( ~ r1_tarski(k1_xboole_0,X24)
        | ~ r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X24,k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X24) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f632,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f519,plain,
    ( spl7_3
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f517,f100])).

fof(f517,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f516,f438])).

fof(f516,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f499,f154])).

fof(f499,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl7_3 ),
    inference(resolution,[],[f231,f158])).

fof(f158,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl7_3 ),
    inference(backward_demodulation,[],[f121,f155])).

fof(f121,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f370,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f347,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f347,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f59,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f59,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f228,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f226,f156])).

fof(f156,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl7_1 ),
    inference(backward_demodulation,[],[f113,f155])).

fof(f113,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f226,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(subsumption_resolution,[],[f225,f60])).

fof(f225,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK4,X0))
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f224,f62])).

fof(f224,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK4,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f97,f155])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f153,plain,
    ( spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f144,f150,f146])).

fof(f144,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f137,f61])).

fof(f61,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,
    ( ~ v1_funct_2(sK4,sK0,sK3)
    | k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4) ),
    inference(resolution,[],[f62,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f122,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f65,f119,f115,f111])).

fof(f65,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:13:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (26279)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.46  % (26295)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.49  % (26267)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (26288)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (26270)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (26280)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (26271)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (26273)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (26272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (26266)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (26281)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.51  % (26287)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (26275)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.51  % (26269)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (26268)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (26288)Refutation not found, incomplete strategy% (26288)------------------------------
% 0.19/0.51  % (26288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (26288)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (26288)Memory used [KB]: 10874
% 0.19/0.51  % (26288)Time elapsed: 0.086 s
% 0.19/0.51  % (26288)------------------------------
% 0.19/0.51  % (26288)------------------------------
% 0.19/0.51  % (26277)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (26278)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (26291)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (26274)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (26294)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (26289)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (26290)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (26293)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.52  % (26292)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (26283)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (26285)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (26286)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (26282)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (26284)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (26276)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.57  % (26274)Refutation found. Thanks to Tanya!
% 0.19/0.57  % SZS status Theorem for theBenchmark
% 0.19/0.57  % SZS output start Proof for theBenchmark
% 0.19/0.57  fof(f1004,plain,(
% 0.19/0.57    $false),
% 0.19/0.57    inference(avatar_sat_refutation,[],[f122,f153,f228,f370,f519,f752,f799,f1001])).
% 0.19/0.57  fof(f1001,plain,(
% 0.19/0.57    spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_31),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f1000])).
% 0.19/0.57  fof(f1000,plain,(
% 0.19/0.57    $false | (spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_31)),
% 0.19/0.57    inference(subsumption_resolution,[],[f999,f100])).
% 0.19/0.57  fof(f100,plain,(
% 0.19/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.57    inference(equality_resolution,[],[f73])).
% 0.19/0.57  fof(f73,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f50])).
% 0.19/0.57  fof(f50,plain,(
% 0.19/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.57    inference(flattening,[],[f49])).
% 0.19/0.57  fof(f49,plain,(
% 0.19/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.57    inference(nnf_transformation,[],[f3])).
% 0.19/0.57  fof(f3,axiom,(
% 0.19/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.57  fof(f999,plain,(
% 0.19/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_31)),
% 0.19/0.57    inference(subsumption_resolution,[],[f998,f778])).
% 0.19/0.57  fof(f778,plain,(
% 0.19/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f594,f765])).
% 0.19/0.57  fof(f765,plain,(
% 0.19/0.57    k1_xboole_0 = sK1 | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(subsumption_resolution,[],[f754,f594])).
% 0.19/0.57  fof(f754,plain,(
% 0.19/0.57    k1_xboole_0 = sK1 | v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(resolution,[],[f735,f100])).
% 0.19/0.57  fof(f735,plain,(
% 0.19/0.57    ( ! [X0] : (~r1_tarski(sK1,X0) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) ) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(subsumption_resolution,[],[f718,f100])).
% 0.19/0.57  fof(f718,plain,(
% 0.19/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(sK1,X0) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) ) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(resolution,[],[f632,f104])).
% 0.19/0.57  fof(f104,plain,(
% 0.19/0.57    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.19/0.57    inference(equality_resolution,[],[f103])).
% 0.19/0.57  fof(f103,plain,(
% 0.19/0.57    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.57    inference(equality_resolution,[],[f93])).
% 0.19/0.57  fof(f93,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f58])).
% 0.19/0.57  fof(f58,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(nnf_transformation,[],[f38])).
% 0.19/0.57  fof(f38,plain,(
% 0.19/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(flattening,[],[f37])).
% 0.19/0.57  fof(f37,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f17])).
% 0.19/0.57  fof(f17,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.57  fof(f632,plain,(
% 0.19/0.57    ( ! [X2,X3] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k1_xboole_0,X3) | ~r1_tarski(sK1,X2)) ) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(forward_demodulation,[],[f631,f587])).
% 0.19/0.57  fof(f587,plain,(
% 0.19/0.57    sK1 = k1_relat_1(k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f438,f583])).
% 0.19/0.57  fof(f583,plain,(
% 0.19/0.57    k1_xboole_0 = k7_relat_1(sK4,sK1) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(resolution,[],[f561,f67])).
% 0.19/0.57  fof(f67,plain,(
% 0.19/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.57    inference(cnf_transformation,[],[f25])).
% 0.19/0.57  fof(f25,plain,(
% 0.19/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.57    inference(ennf_transformation,[],[f4])).
% 0.19/0.57  fof(f4,axiom,(
% 0.19/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.57  fof(f561,plain,(
% 0.19/0.57    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(forward_demodulation,[],[f560,f101])).
% 0.19/0.57  fof(f101,plain,(
% 0.19/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.57    inference(equality_resolution,[],[f83])).
% 0.19/0.57  fof(f83,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f57])).
% 0.19/0.57  fof(f57,plain,(
% 0.19/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.57    inference(flattening,[],[f56])).
% 0.19/0.57  fof(f56,plain,(
% 0.19/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.57    inference(nnf_transformation,[],[f5])).
% 0.19/0.57  fof(f5,axiom,(
% 0.19/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.57  fof(f560,plain,(
% 0.19/0.57    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(forward_demodulation,[],[f532,f545])).
% 0.19/0.57  fof(f545,plain,(
% 0.19/0.57    k1_xboole_0 = sK2 | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(subsumption_resolution,[],[f544,f157])).
% 0.19/0.57  fof(f157,plain,(
% 0.19/0.57    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl7_2),
% 0.19/0.57    inference(backward_demodulation,[],[f117,f155])).
% 0.19/0.57  fof(f155,plain,(
% 0.19/0.57    ( ! [X1] : (k2_partfun1(sK0,sK3,sK4,X1) = k7_relat_1(sK4,X1)) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f140,f60])).
% 0.19/0.57  fof(f60,plain,(
% 0.19/0.57    v1_funct_1(sK4)),
% 0.19/0.57    inference(cnf_transformation,[],[f47])).
% 0.19/0.57  fof(f47,plain,(
% 0.19/0.57    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 0.19/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f46,f45])).
% 0.19/0.57  fof(f45,plain,(
% 0.19/0.57    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 0.19/0.57    introduced(choice_axiom,[])).
% 0.19/0.57  fof(f46,plain,(
% 0.19/0.57    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 0.19/0.57    introduced(choice_axiom,[])).
% 0.19/0.57  fof(f24,plain,(
% 0.19/0.57    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.19/0.57    inference(flattening,[],[f23])).
% 0.19/0.57  fof(f23,plain,(
% 0.19/0.57    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.19/0.57    inference(ennf_transformation,[],[f21])).
% 0.19/0.57  fof(f21,negated_conjecture,(
% 0.19/0.57    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.19/0.57    inference(negated_conjecture,[],[f20])).
% 0.19/0.57  fof(f20,conjecture,(
% 0.19/0.57    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 0.19/0.57  fof(f140,plain,(
% 0.19/0.57    ( ! [X1] : (k2_partfun1(sK0,sK3,sK4,X1) = k7_relat_1(sK4,X1) | ~v1_funct_1(sK4)) )),
% 0.19/0.57    inference(resolution,[],[f62,f96])).
% 0.19/0.57  fof(f96,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f42])).
% 0.19/0.57  fof(f42,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.57    inference(flattening,[],[f41])).
% 0.19/0.57  fof(f41,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.57    inference(ennf_transformation,[],[f19])).
% 0.19/0.57  fof(f19,axiom,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.19/0.57  fof(f62,plain,(
% 0.19/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.19/0.57    inference(cnf_transformation,[],[f47])).
% 0.19/0.57  fof(f117,plain,(
% 0.19/0.57    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl7_2),
% 0.19/0.57    inference(avatar_component_clause,[],[f115])).
% 0.19/0.57  fof(f115,plain,(
% 0.19/0.57    spl7_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.19/0.57  fof(f544,plain,(
% 0.19/0.57    k1_xboole_0 = sK2 | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(subsumption_resolution,[],[f528,f543])).
% 0.19/0.57  fof(f543,plain,(
% 0.19/0.57    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(forward_demodulation,[],[f525,f438])).
% 0.19/0.57  fof(f525,plain,(
% 0.19/0.57    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl7_3),
% 0.19/0.57    inference(resolution,[],[f522,f86])).
% 0.19/0.57  fof(f86,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f35])).
% 0.19/0.57  fof(f35,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f14])).
% 0.19/0.57  fof(f14,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.57  fof(f522,plain,(
% 0.19/0.57    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_3),
% 0.19/0.57    inference(forward_demodulation,[],[f120,f155])).
% 0.19/0.57  fof(f120,plain,(
% 0.19/0.57    m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_3),
% 0.19/0.57    inference(avatar_component_clause,[],[f119])).
% 0.19/0.57  fof(f119,plain,(
% 0.19/0.57    spl7_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.19/0.57  fof(f528,plain,(
% 0.19/0.57    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl7_3),
% 0.19/0.57    inference(resolution,[],[f522,f90])).
% 0.19/0.57  fof(f90,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f58])).
% 0.19/0.57  fof(f532,plain,(
% 0.19/0.57    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl7_3),
% 0.19/0.57    inference(resolution,[],[f522,f79])).
% 0.19/0.57  fof(f79,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f55])).
% 0.19/0.57  fof(f55,plain,(
% 0.19/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.57    inference(nnf_transformation,[],[f6])).
% 0.19/0.57  fof(f6,axiom,(
% 0.19/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.57  fof(f438,plain,(
% 0.19/0.57    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl7_6),
% 0.19/0.57    inference(resolution,[],[f406,f63])).
% 0.19/0.57  fof(f63,plain,(
% 0.19/0.57    r1_tarski(sK1,sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f47])).
% 0.19/0.57  fof(f406,plain,(
% 0.19/0.57    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | ~spl7_6),
% 0.19/0.57    inference(subsumption_resolution,[],[f404,f134])).
% 0.19/0.57  fof(f134,plain,(
% 0.19/0.57    v1_relat_1(sK4)),
% 0.19/0.57    inference(resolution,[],[f62,f85])).
% 0.19/0.57  fof(f85,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f34])).
% 0.19/0.57  fof(f34,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f11])).
% 0.19/0.57  fof(f11,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.57  fof(f404,plain,(
% 0.19/0.57    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK4,X1)) = X1 | ~v1_relat_1(sK4)) ) | ~spl7_6),
% 0.19/0.57    inference(superposition,[],[f69,f387])).
% 0.19/0.57  fof(f387,plain,(
% 0.19/0.57    sK0 = k1_relat_1(sK4) | ~spl7_6),
% 0.19/0.57    inference(backward_demodulation,[],[f135,f148])).
% 0.19/0.57  fof(f148,plain,(
% 0.19/0.57    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl7_6),
% 0.19/0.57    inference(avatar_component_clause,[],[f146])).
% 0.19/0.57  fof(f146,plain,(
% 0.19/0.57    spl7_6 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.19/0.57  fof(f135,plain,(
% 0.19/0.57    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 0.19/0.57    inference(resolution,[],[f62,f86])).
% 0.19/0.57  fof(f69,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f28])).
% 0.19/0.57  fof(f28,plain,(
% 0.19/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.57    inference(flattening,[],[f27])).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f10])).
% 0.19/0.57  fof(f10,axiom,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.19/0.57  fof(f631,plain,(
% 0.19/0.57    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,X3) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k1_relat_1(k1_xboole_0),X2)) ) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(forward_demodulation,[],[f618,f569])).
% 0.19/0.57  fof(f569,plain,(
% 0.19/0.57    k1_xboole_0 = k9_relat_1(sK4,sK1) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(resolution,[],[f551,f67])).
% 0.19/0.57  fof(f551,plain,(
% 0.19/0.57    r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f154,f545])).
% 0.19/0.57  fof(f154,plain,(
% 0.19/0.57    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.19/0.57    inference(backward_demodulation,[],[f64,f139])).
% 0.19/0.57  fof(f139,plain,(
% 0.19/0.57    ( ! [X0] : (k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 0.19/0.57    inference(resolution,[],[f62,f95])).
% 0.19/0.57  fof(f95,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f40])).
% 0.19/0.57  fof(f40,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f15])).
% 0.19/0.57  fof(f15,axiom,(
% 0.19/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.57  fof(f64,plain,(
% 0.19/0.57    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.19/0.57    inference(cnf_transformation,[],[f47])).
% 0.19/0.57  fof(f618,plain,(
% 0.19/0.57    ( ! [X2,X3] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k9_relat_1(sK4,sK1),X3) | ~r1_tarski(k1_relat_1(k1_xboole_0),X2)) ) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(superposition,[],[f231,f583])).
% 0.19/0.57  fof(f231,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k9_relat_1(sK4,X0),X1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2)) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f230,f204])).
% 0.19/0.57  fof(f204,plain,(
% 0.19/0.57    ( ! [X1] : (v1_relat_1(k7_relat_1(sK4,X1))) )),
% 0.19/0.57    inference(resolution,[],[f160,f85])).
% 0.19/0.57  fof(f160,plain,(
% 0.19/0.57    ( ! [X2] : (m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 0.19/0.57    inference(forward_demodulation,[],[f159,f155])).
% 0.19/0.57  fof(f159,plain,(
% 0.19/0.57    ( ! [X2] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f141,f60])).
% 0.19/0.57  fof(f141,plain,(
% 0.19/0.57    ( ! [X2] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) )),
% 0.19/0.57    inference(resolution,[],[f62,f98])).
% 0.19/0.57  fof(f98,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f44])).
% 0.19/0.57  fof(f44,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.57    inference(flattening,[],[f43])).
% 0.19/0.57  fof(f43,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.57    inference(ennf_transformation,[],[f18])).
% 0.19/0.57  fof(f18,axiom,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.19/0.57  fof(f230,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(sK4,X0),X1) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2) | ~v1_relat_1(k7_relat_1(sK4,X0))) )),
% 0.19/0.57    inference(superposition,[],[f84,f171])).
% 0.19/0.57  fof(f171,plain,(
% 0.19/0.57    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) )),
% 0.19/0.57    inference(resolution,[],[f134,f68])).
% 0.19/0.57  fof(f68,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f26])).
% 0.19/0.57  fof(f26,plain,(
% 0.19/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f9])).
% 0.19/0.57  fof(f9,axiom,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.57  fof(f84,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f33])).
% 0.19/0.57  fof(f33,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.19/0.57    inference(flattening,[],[f32])).
% 0.19/0.57  fof(f32,plain,(
% 0.19/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.19/0.57    inference(ennf_transformation,[],[f16])).
% 0.19/0.57  fof(f16,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.19/0.57  fof(f594,plain,(
% 0.19/0.57    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f550,f583])).
% 0.19/0.57  fof(f550,plain,(
% 0.19/0.57    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f157,f545])).
% 0.19/0.57  fof(f998,plain,(
% 0.19/0.57    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_31)),
% 0.19/0.57    inference(trivial_inequality_removal,[],[f993])).
% 0.19/0.57  fof(f993,plain,(
% 0.19/0.57    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_31)),
% 0.19/0.57    inference(superposition,[],[f751,f777])).
% 0.19/0.57  fof(f777,plain,(
% 0.19/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f593,f765])).
% 0.19/0.57  fof(f593,plain,(
% 0.19/0.57    sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f546,f583])).
% 0.19/0.57  fof(f546,plain,(
% 0.19/0.57    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(backward_demodulation,[],[f543,f545])).
% 0.19/0.57  fof(f751,plain,(
% 0.19/0.57    ( ! [X24] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X24,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X24) | ~r1_tarski(k1_xboole_0,X24)) ) | ~spl7_31),
% 0.19/0.57    inference(avatar_component_clause,[],[f750])).
% 0.19/0.57  fof(f750,plain,(
% 0.19/0.57    spl7_31 <=> ! [X24] : (~r1_tarski(k1_xboole_0,X24) | v1_funct_2(k1_xboole_0,k1_xboole_0,X24) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X24,k1_xboole_0))),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.19/0.57  fof(f799,plain,(
% 0.19/0.57    spl7_2 | ~spl7_3 | ~spl7_6 | spl7_29),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f798])).
% 0.19/0.57  fof(f798,plain,(
% 0.19/0.57    $false | (spl7_2 | ~spl7_3 | ~spl7_6 | spl7_29)),
% 0.19/0.57    inference(subsumption_resolution,[],[f792,f100])).
% 0.19/0.57  fof(f792,plain,(
% 0.19/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_6 | spl7_29)),
% 0.19/0.57    inference(backward_demodulation,[],[f744,f765])).
% 0.19/0.57  fof(f744,plain,(
% 0.19/0.57    ~r1_tarski(sK1,k1_xboole_0) | spl7_29),
% 0.19/0.57    inference(avatar_component_clause,[],[f742])).
% 0.19/0.57  fof(f742,plain,(
% 0.19/0.57    spl7_29 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.19/0.57  fof(f752,plain,(
% 0.19/0.57    ~spl7_29 | spl7_31 | spl7_2 | ~spl7_3 | ~spl7_6),
% 0.19/0.57    inference(avatar_split_clause,[],[f730,f146,f119,f115,f750,f742])).
% 0.19/0.57  fof(f730,plain,(
% 0.19/0.57    ( ! [X24] : (~r1_tarski(k1_xboole_0,X24) | ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X24,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X24)) ) | (spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(resolution,[],[f632,f106])).
% 0.19/0.57  fof(f106,plain,(
% 0.19/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.19/0.57    inference(equality_resolution,[],[f91])).
% 0.19/0.57  fof(f91,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f58])).
% 0.19/0.57  fof(f519,plain,(
% 0.19/0.57    spl7_3 | ~spl7_6),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f518])).
% 0.19/0.57  fof(f518,plain,(
% 0.19/0.57    $false | (spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(subsumption_resolution,[],[f517,f100])).
% 0.19/0.57  fof(f517,plain,(
% 0.19/0.57    ~r1_tarski(sK1,sK1) | (spl7_3 | ~spl7_6)),
% 0.19/0.57    inference(forward_demodulation,[],[f516,f438])).
% 0.19/0.57  fof(f516,plain,(
% 0.19/0.57    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl7_3),
% 0.19/0.57    inference(subsumption_resolution,[],[f499,f154])).
% 0.19/0.57  fof(f499,plain,(
% 0.19/0.57    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl7_3),
% 0.19/0.57    inference(resolution,[],[f231,f158])).
% 0.19/0.57  fof(f158,plain,(
% 0.19/0.57    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl7_3),
% 0.19/0.57    inference(backward_demodulation,[],[f121,f155])).
% 0.19/0.57  fof(f121,plain,(
% 0.19/0.57    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl7_3),
% 0.19/0.57    inference(avatar_component_clause,[],[f119])).
% 0.19/0.57  fof(f370,plain,(
% 0.19/0.57    ~spl7_7),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f369])).
% 0.19/0.57  fof(f369,plain,(
% 0.19/0.57    $false | ~spl7_7),
% 0.19/0.57    inference(subsumption_resolution,[],[f347,f66])).
% 0.19/0.57  fof(f66,plain,(
% 0.19/0.57    v1_xboole_0(k1_xboole_0)),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f2,axiom,(
% 0.19/0.57    v1_xboole_0(k1_xboole_0)),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.59  fof(f347,plain,(
% 0.19/0.59    ~v1_xboole_0(k1_xboole_0) | ~spl7_7),
% 0.19/0.59    inference(backward_demodulation,[],[f59,f152])).
% 0.19/0.59  fof(f152,plain,(
% 0.19/0.59    k1_xboole_0 = sK3 | ~spl7_7),
% 0.19/0.59    inference(avatar_component_clause,[],[f150])).
% 0.19/0.59  fof(f150,plain,(
% 0.19/0.59    spl7_7 <=> k1_xboole_0 = sK3),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.19/0.59  fof(f59,plain,(
% 0.19/0.59    ~v1_xboole_0(sK3)),
% 0.19/0.59    inference(cnf_transformation,[],[f47])).
% 0.19/0.59  fof(f228,plain,(
% 0.19/0.59    spl7_1),
% 0.19/0.59    inference(avatar_contradiction_clause,[],[f227])).
% 0.19/0.59  fof(f227,plain,(
% 0.19/0.59    $false | spl7_1),
% 0.19/0.59    inference(resolution,[],[f226,f156])).
% 0.19/0.59  fof(f156,plain,(
% 0.19/0.59    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl7_1),
% 0.19/0.59    inference(backward_demodulation,[],[f113,f155])).
% 0.19/0.59  fof(f113,plain,(
% 0.19/0.59    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl7_1),
% 0.19/0.59    inference(avatar_component_clause,[],[f111])).
% 0.19/0.59  fof(f111,plain,(
% 0.19/0.59    spl7_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.59  fof(f226,plain,(
% 0.19/0.59    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 0.19/0.59    inference(subsumption_resolution,[],[f225,f60])).
% 0.19/0.59  fof(f225,plain,(
% 0.19/0.59    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0)) | ~v1_funct_1(sK4)) )),
% 0.19/0.59    inference(subsumption_resolution,[],[f224,f62])).
% 0.19/0.59  fof(f224,plain,(
% 0.19/0.59    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) )),
% 0.19/0.59    inference(superposition,[],[f97,f155])).
% 0.19/0.59  fof(f97,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f44])).
% 0.19/0.59  fof(f153,plain,(
% 0.19/0.59    spl7_6 | spl7_7),
% 0.19/0.59    inference(avatar_split_clause,[],[f144,f150,f146])).
% 0.19/0.59  fof(f144,plain,(
% 0.19/0.59    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.19/0.59    inference(subsumption_resolution,[],[f137,f61])).
% 0.19/0.59  fof(f61,plain,(
% 0.19/0.59    v1_funct_2(sK4,sK0,sK3)),
% 0.19/0.59    inference(cnf_transformation,[],[f47])).
% 0.19/0.59  fof(f137,plain,(
% 0.19/0.59    ~v1_funct_2(sK4,sK0,sK3) | k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.19/0.59    inference(resolution,[],[f62,f88])).
% 0.19/0.59  fof(f88,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.19/0.59    inference(cnf_transformation,[],[f58])).
% 0.19/0.59  fof(f122,plain,(
% 0.19/0.59    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.19/0.59    inference(avatar_split_clause,[],[f65,f119,f115,f111])).
% 0.19/0.59  fof(f65,plain,(
% 0.19/0.59    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.19/0.59    inference(cnf_transformation,[],[f47])).
% 0.19/0.59  % SZS output end Proof for theBenchmark
% 0.19/0.59  % (26274)------------------------------
% 0.19/0.59  % (26274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (26274)Termination reason: Refutation
% 0.19/0.59  
% 0.19/0.59  % (26274)Memory used [KB]: 11257
% 0.19/0.59  % (26274)Time elapsed: 0.190 s
% 0.19/0.59  % (26274)------------------------------
% 0.19/0.59  % (26274)------------------------------
% 0.19/0.59  % (26265)Success in time 0.248 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:07:15 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 543 expanded)
%              Number of leaves         :   25 ( 209 expanded)
%              Depth                    :   19
%              Number of atoms          :  446 (4672 expanded)
%              Number of equality atoms :   56 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f134,f585,f890,f1355])).

fof(f1355,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f1354])).

fof(f1354,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f1353,f149])).

fof(f149,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f146,f86])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f146,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f85,f77])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f60,f65,f64,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ? [X4] :
          ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X4] :
        ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1353,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f1352,f75])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f1352,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f1351,f1340])).

fof(f1340,plain,
    ( r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_17 ),
    inference(resolution,[],[f606,f140])).

fof(f140,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f101,f78])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f606,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK0)
        | r1_tarski(X4,k1_relat_1(sK2)) )
    | ~ spl5_17 ),
    inference(resolution,[],[f343,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f343,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl5_17
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1351,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f895,f893])).

fof(f893,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_2 ),
    inference(forward_demodulation,[],[f132,f216])).

fof(f216,plain,(
    ! [X3] : k8_relset_1(sK0,sK1,sK2,X3) = k10_relat_1(sK2,X3) ),
    inference(resolution,[],[f116,f77])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f132,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_2
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f895,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f894,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f894,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f127,f220])).

fof(f220,plain,(
    ! [X3] : k7_relset_1(sK0,sK1,sK2,X3) = k9_relat_1(sK2,X3) ),
    inference(resolution,[],[f117,f77])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f127,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_1
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f890,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f889])).

fof(f889,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f883,f375])).

fof(f375,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_1 ),
    inference(superposition,[],[f128,f220])).

fof(f128,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f883,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f353,f403])).

fof(f403,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f400,f216])).

fof(f400,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k8_relset_1(sK0,sK1,sK2,sK4)))
    | ~ spl5_2 ),
    inference(resolution,[],[f197,f149])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,k8_relset_1(sK0,sK1,sK2,sK4))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f106,f131])).

fof(f131,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f353,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,k9_relat_1(sK2,k10_relat_1(sK2,X9)))
      | r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f194,f115])).

fof(f194,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(subsumption_resolution,[],[f193,f149])).

fof(f193,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f94,f75])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f585,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f562,f82])).

fof(f82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f562,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_17 ),
    inference(superposition,[],[f74,f561])).

fof(f561,plain,
    ( k1_xboole_0 = sK1
    | spl5_17 ),
    inference(subsumption_resolution,[],[f560,f344])).

fof(f344,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f342])).

fof(f560,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f559,f280])).

fof(f280,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f279,f202])).

fof(f202,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f107,f77])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f279,plain,(
    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f278,f216])).

fof(f278,plain,(
    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f277,f230])).

fof(f230,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f229,f206])).

fof(f206,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f108,f77])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f229,plain,(
    k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f224,f220])).

fof(f224,plain,(
    k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(resolution,[],[f110,f77])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f277,plain,(
    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f270,f220])).

fof(f270,plain,(
    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(resolution,[],[f113,f77])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f559,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k2_relat_1(sK2)))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f558,f230])).

fof(f558,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f557,f220])).

fof(f557,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f556,f216])).

fof(f556,plain,
    ( r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f555,f75])).

fof(f555,plain,
    ( r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f550,f76])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f550,plain,
    ( r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f285,f77])).

fof(f285,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
      | r1_tarski(X6,k8_relset_1(X6,X5,X7,k7_relset_1(X6,X5,X7,X6)))
      | k1_xboole_0 = X5
      | ~ v1_funct_2(X7,X6,X5)
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f118,f120])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f134,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f80,f130,f126])).

fof(f80,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f133,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f81,f130,f126])).

fof(f81,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (1148)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (1122)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (1120)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (1123)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (1121)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (1145)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (1144)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (1133)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (1132)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (1143)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (1124)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (1125)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (1146)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (1138)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (1129)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (1147)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (1127)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (1130)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (1140)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (1139)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (1142)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (1134)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (1141)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.55  % (1149)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (1131)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.45/0.56  % (1128)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.69/0.61  % (1131)Refutation found. Thanks to Tanya!
% 1.69/0.61  % SZS status Theorem for theBenchmark
% 1.69/0.61  % SZS output start Proof for theBenchmark
% 1.69/0.61  fof(f1356,plain,(
% 1.69/0.61    $false),
% 1.69/0.61    inference(avatar_sat_refutation,[],[f133,f134,f585,f890,f1355])).
% 1.69/0.61  fof(f1355,plain,(
% 1.69/0.61    ~spl5_1 | spl5_2 | ~spl5_17),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f1354])).
% 1.69/0.61  fof(f1354,plain,(
% 1.69/0.61    $false | (~spl5_1 | spl5_2 | ~spl5_17)),
% 1.69/0.61    inference(subsumption_resolution,[],[f1353,f149])).
% 1.69/0.61  fof(f149,plain,(
% 1.69/0.61    v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f146,f86])).
% 1.69/0.61  fof(f86,plain,(
% 1.69/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f11])).
% 1.69/0.61  fof(f11,axiom,(
% 1.69/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.69/0.61  fof(f146,plain,(
% 1.69/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.69/0.61    inference(resolution,[],[f85,f77])).
% 1.69/0.61  fof(f77,plain,(
% 1.69/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  fof(f66,plain,(
% 1.69/0.61    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f60,f65,f64,f63,f62,f61])).
% 1.69/0.61  fof(f61,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f62,plain,(
% 1.69/0.61    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f63,plain,(
% 1.69/0.61    ? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f64,plain,(
% 1.69/0.61    ? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f65,plain,(
% 1.69/0.61    ? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f60,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.69/0.61    inference(flattening,[],[f59])).
% 1.69/0.61  fof(f59,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.69/0.61    inference(nnf_transformation,[],[f32])).
% 1.69/0.61  fof(f32,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.69/0.61    inference(flattening,[],[f31])).
% 1.69/0.61  fof(f31,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f28])).
% 1.69/0.61  fof(f28,negated_conjecture,(
% 1.69/0.61    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 1.69/0.61    inference(negated_conjecture,[],[f27])).
% 1.69/0.61  fof(f27,conjecture,(
% 1.69/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).
% 1.69/0.61  fof(f85,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f33])).
% 1.69/0.61  fof(f33,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f9])).
% 1.69/0.61  fof(f9,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.69/0.61  fof(f1353,plain,(
% 1.69/0.61    ~v1_relat_1(sK2) | (~spl5_1 | spl5_2 | ~spl5_17)),
% 1.69/0.61    inference(subsumption_resolution,[],[f1352,f75])).
% 1.69/0.61  fof(f75,plain,(
% 1.69/0.61    v1_funct_1(sK2)),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  fof(f1352,plain,(
% 1.69/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_1 | spl5_2 | ~spl5_17)),
% 1.69/0.61    inference(subsumption_resolution,[],[f1351,f1340])).
% 1.69/0.61  fof(f1340,plain,(
% 1.69/0.61    r1_tarski(sK3,k1_relat_1(sK2)) | ~spl5_17),
% 1.69/0.61    inference(resolution,[],[f606,f140])).
% 1.69/0.61  fof(f140,plain,(
% 1.69/0.61    r1_tarski(sK3,sK0)),
% 1.69/0.61    inference(resolution,[],[f101,f78])).
% 1.69/0.61  fof(f78,plain,(
% 1.69/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  fof(f101,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f70])).
% 1.69/0.61  fof(f70,plain,(
% 1.69/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.69/0.61    inference(nnf_transformation,[],[f7])).
% 1.69/0.61  fof(f7,axiom,(
% 1.69/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.69/0.61  fof(f606,plain,(
% 1.69/0.61    ( ! [X4] : (~r1_tarski(X4,sK0) | r1_tarski(X4,k1_relat_1(sK2))) ) | ~spl5_17),
% 1.69/0.61    inference(resolution,[],[f343,f115])).
% 1.69/0.61  fof(f115,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f54])).
% 1.69/0.61  fof(f54,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.69/0.61    inference(flattening,[],[f53])).
% 1.69/0.61  fof(f53,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.69/0.61    inference(ennf_transformation,[],[f3])).
% 1.69/0.61  fof(f3,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.69/0.61  fof(f343,plain,(
% 1.69/0.61    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl5_17),
% 1.69/0.61    inference(avatar_component_clause,[],[f342])).
% 1.69/0.61  fof(f342,plain,(
% 1.69/0.61    spl5_17 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.69/0.61  fof(f1351,plain,(
% 1.69/0.61    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_1 | spl5_2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f895,f893])).
% 1.69/0.61  fof(f893,plain,(
% 1.69/0.61    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_2),
% 1.69/0.61    inference(forward_demodulation,[],[f132,f216])).
% 1.69/0.61  fof(f216,plain,(
% 1.69/0.61    ( ! [X3] : (k8_relset_1(sK0,sK1,sK2,X3) = k10_relat_1(sK2,X3)) )),
% 1.69/0.61    inference(resolution,[],[f116,f77])).
% 1.69/0.61  fof(f116,plain,(
% 1.69/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f55])).
% 1.69/0.61  fof(f55,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(ennf_transformation,[],[f21])).
% 1.69/0.61  fof(f21,axiom,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.69/0.61  fof(f132,plain,(
% 1.69/0.61    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl5_2),
% 1.69/0.61    inference(avatar_component_clause,[],[f130])).
% 1.69/0.61  fof(f130,plain,(
% 1.69/0.61    spl5_2 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.69/0.61  fof(f895,plain,(
% 1.69/0.61    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_1),
% 1.69/0.61    inference(resolution,[],[f894,f114])).
% 1.69/0.61  fof(f114,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f52])).
% 1.69/0.61  fof(f52,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.69/0.61    inference(flattening,[],[f51])).
% 1.69/0.61  fof(f51,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.69/0.61    inference(ennf_transformation,[],[f15])).
% 1.69/0.61  fof(f15,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.69/0.61  fof(f894,plain,(
% 1.69/0.61    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_1),
% 1.69/0.61    inference(forward_demodulation,[],[f127,f220])).
% 1.69/0.61  fof(f220,plain,(
% 1.69/0.61    ( ! [X3] : (k7_relset_1(sK0,sK1,sK2,X3) = k9_relat_1(sK2,X3)) )),
% 1.69/0.61    inference(resolution,[],[f117,f77])).
% 1.69/0.61  fof(f117,plain,(
% 1.69/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f56])).
% 1.69/0.61  fof(f56,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(ennf_transformation,[],[f20])).
% 1.69/0.61  fof(f20,axiom,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.69/0.61  fof(f127,plain,(
% 1.69/0.61    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_1),
% 1.69/0.61    inference(avatar_component_clause,[],[f126])).
% 1.69/0.61  fof(f126,plain,(
% 1.69/0.61    spl5_1 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.69/0.61  fof(f890,plain,(
% 1.69/0.61    spl5_1 | ~spl5_2),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f889])).
% 1.69/0.61  fof(f889,plain,(
% 1.69/0.61    $false | (spl5_1 | ~spl5_2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f883,f375])).
% 1.69/0.61  fof(f375,plain,(
% 1.69/0.61    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_1),
% 1.69/0.61    inference(superposition,[],[f128,f220])).
% 1.69/0.61  fof(f128,plain,(
% 1.69/0.61    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl5_1),
% 1.69/0.61    inference(avatar_component_clause,[],[f126])).
% 1.69/0.61  fof(f883,plain,(
% 1.69/0.61    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_2),
% 1.69/0.61    inference(resolution,[],[f353,f403])).
% 1.69/0.61  fof(f403,plain,(
% 1.69/0.61    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl5_2),
% 1.69/0.61    inference(forward_demodulation,[],[f400,f216])).
% 1.69/0.61  fof(f400,plain,(
% 1.69/0.61    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k8_relset_1(sK0,sK1,sK2,sK4))) | ~spl5_2),
% 1.69/0.61    inference(resolution,[],[f197,f149])).
% 1.69/0.61  fof(f197,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,k8_relset_1(sK0,sK1,sK2,sK4)))) ) | ~spl5_2),
% 1.69/0.61    inference(resolution,[],[f106,f131])).
% 1.69/0.61  fof(f131,plain,(
% 1.69/0.61    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_2),
% 1.69/0.61    inference(avatar_component_clause,[],[f130])).
% 1.69/0.61  fof(f106,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f45])).
% 1.69/0.61  fof(f45,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.69/0.61    inference(flattening,[],[f44])).
% 1.69/0.61  fof(f44,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.69/0.61    inference(ennf_transformation,[],[f12])).
% 1.69/0.61  fof(f12,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.69/0.61  fof(f353,plain,(
% 1.69/0.61    ( ! [X8,X9] : (~r1_tarski(X8,k9_relat_1(sK2,k10_relat_1(sK2,X9))) | r1_tarski(X8,X9)) )),
% 1.69/0.61    inference(resolution,[],[f194,f115])).
% 1.69/0.61  fof(f194,plain,(
% 1.69/0.61    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f193,f149])).
% 1.69/0.61  fof(f193,plain,(
% 1.69/0.61    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) | ~v1_relat_1(sK2)) )),
% 1.69/0.61    inference(resolution,[],[f94,f75])).
% 1.69/0.61  fof(f94,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f41])).
% 1.69/0.61  fof(f41,plain,(
% 1.69/0.61    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.69/0.61    inference(flattening,[],[f40])).
% 1.69/0.61  fof(f40,plain,(
% 1.69/0.61    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.69/0.61    inference(ennf_transformation,[],[f14])).
% 1.69/0.61  fof(f14,axiom,(
% 1.69/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.69/0.61  fof(f585,plain,(
% 1.69/0.61    spl5_17),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f584])).
% 1.69/0.61  fof(f584,plain,(
% 1.69/0.61    $false | spl5_17),
% 1.69/0.61    inference(subsumption_resolution,[],[f562,f82])).
% 1.69/0.61  fof(f82,plain,(
% 1.69/0.61    v1_xboole_0(k1_xboole_0)),
% 1.69/0.61    inference(cnf_transformation,[],[f1])).
% 1.69/0.61  fof(f1,axiom,(
% 1.69/0.61    v1_xboole_0(k1_xboole_0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.69/0.61  fof(f562,plain,(
% 1.69/0.61    ~v1_xboole_0(k1_xboole_0) | spl5_17),
% 1.69/0.61    inference(superposition,[],[f74,f561])).
% 1.69/0.61  fof(f561,plain,(
% 1.69/0.61    k1_xboole_0 = sK1 | spl5_17),
% 1.69/0.61    inference(subsumption_resolution,[],[f560,f344])).
% 1.69/0.61  fof(f344,plain,(
% 1.69/0.61    ~r1_tarski(sK0,k1_relat_1(sK2)) | spl5_17),
% 1.69/0.61    inference(avatar_component_clause,[],[f342])).
% 1.69/0.61  fof(f560,plain,(
% 1.69/0.61    r1_tarski(sK0,k1_relat_1(sK2)) | k1_xboole_0 = sK1),
% 1.69/0.61    inference(forward_demodulation,[],[f559,f280])).
% 1.69/0.61  fof(f280,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.69/0.61    inference(forward_demodulation,[],[f279,f202])).
% 1.69/0.61  fof(f202,plain,(
% 1.69/0.61    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.69/0.61    inference(resolution,[],[f107,f77])).
% 1.69/0.61  fof(f107,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f46])).
% 1.69/0.61  fof(f46,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(ennf_transformation,[],[f18])).
% 1.69/0.61  fof(f18,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.69/0.61  fof(f279,plain,(
% 1.69/0.61    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.69/0.61    inference(forward_demodulation,[],[f278,f216])).
% 1.69/0.61  fof(f278,plain,(
% 1.69/0.61    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2))),
% 1.69/0.61    inference(forward_demodulation,[],[f277,f230])).
% 1.69/0.61  fof(f230,plain,(
% 1.69/0.61    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 1.69/0.61    inference(forward_demodulation,[],[f229,f206])).
% 1.69/0.61  fof(f206,plain,(
% 1.69/0.61    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.69/0.61    inference(resolution,[],[f108,f77])).
% 1.69/0.61  fof(f108,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f47])).
% 1.69/0.61  fof(f47,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(ennf_transformation,[],[f19])).
% 1.69/0.61  fof(f19,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.69/0.61  fof(f229,plain,(
% 1.69/0.61    k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0)),
% 1.69/0.61    inference(forward_demodulation,[],[f224,f220])).
% 1.69/0.61  fof(f224,plain,(
% 1.69/0.61    k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 1.69/0.61    inference(resolution,[],[f110,f77])).
% 1.69/0.61  fof(f110,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f49])).
% 1.69/0.61  fof(f49,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.61    inference(ennf_transformation,[],[f22])).
% 1.69/0.61  fof(f22,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.69/0.61  fof(f277,plain,(
% 1.69/0.61    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0))),
% 1.69/0.61    inference(forward_demodulation,[],[f270,f220])).
% 1.69/0.61  fof(f270,plain,(
% 1.69/0.61    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 1.69/0.61    inference(resolution,[],[f113,f77])).
% 1.69/0.61  fof(f113,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f50])).
% 1.69/0.61  fof(f50,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.69/0.61    inference(ennf_transformation,[],[f23])).
% 1.69/0.61  fof(f23,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.69/0.61  fof(f559,plain,(
% 1.69/0.61    r1_tarski(sK0,k10_relat_1(sK2,k2_relat_1(sK2))) | k1_xboole_0 = sK1),
% 1.69/0.61    inference(forward_demodulation,[],[f558,f230])).
% 1.69/0.61  fof(f558,plain,(
% 1.69/0.61    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k1_xboole_0 = sK1),
% 1.69/0.61    inference(forward_demodulation,[],[f557,f220])).
% 1.69/0.61  fof(f557,plain,(
% 1.69/0.61    r1_tarski(sK0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0))) | k1_xboole_0 = sK1),
% 1.69/0.61    inference(forward_demodulation,[],[f556,f216])).
% 1.69/0.61  fof(f556,plain,(
% 1.69/0.61    r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))) | k1_xboole_0 = sK1),
% 1.69/0.61    inference(subsumption_resolution,[],[f555,f75])).
% 1.69/0.61  fof(f555,plain,(
% 1.69/0.61    r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f550,f76])).
% 1.69/0.61  fof(f76,plain,(
% 1.69/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  fof(f550,plain,(
% 1.69/0.61    r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.69/0.61    inference(resolution,[],[f285,f77])).
% 1.69/0.61  fof(f285,plain,(
% 1.69/0.61    ( ! [X6,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | r1_tarski(X6,k8_relset_1(X6,X5,X7,k7_relset_1(X6,X5,X7,X6))) | k1_xboole_0 = X5 | ~v1_funct_2(X7,X6,X5) | ~v1_funct_1(X7)) )),
% 1.69/0.61    inference(resolution,[],[f118,f120])).
% 1.69/0.61  fof(f120,plain,(
% 1.69/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.61    inference(equality_resolution,[],[f99])).
% 1.69/0.61  fof(f99,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.61    inference(cnf_transformation,[],[f69])).
% 1.69/0.61  fof(f69,plain,(
% 1.69/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.61    inference(flattening,[],[f68])).
% 1.69/0.61  fof(f68,plain,(
% 1.69/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.61    inference(nnf_transformation,[],[f2])).
% 1.69/0.61  fof(f2,axiom,(
% 1.69/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.61  fof(f118,plain,(
% 1.69/0.61    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X0) | k1_xboole_0 = X1 | r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f58])).
% 1.69/0.61  fof(f58,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.69/0.61    inference(flattening,[],[f57])).
% 1.69/0.61  fof(f57,plain,(
% 1.69/0.61    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.69/0.61    inference(ennf_transformation,[],[f26])).
% 1.69/0.61  fof(f26,axiom,(
% 1.69/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).
% 1.69/0.61  fof(f74,plain,(
% 1.69/0.61    ~v1_xboole_0(sK1)),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  fof(f134,plain,(
% 1.69/0.61    spl5_1 | spl5_2),
% 1.69/0.61    inference(avatar_split_clause,[],[f80,f130,f126])).
% 1.69/0.61  fof(f80,plain,(
% 1.69/0.61    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  fof(f133,plain,(
% 1.69/0.61    ~spl5_1 | ~spl5_2),
% 1.69/0.61    inference(avatar_split_clause,[],[f81,f130,f126])).
% 1.69/0.61  fof(f81,plain,(
% 1.69/0.61    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 1.69/0.61    inference(cnf_transformation,[],[f66])).
% 1.69/0.61  % SZS output end Proof for theBenchmark
% 1.69/0.61  % (1131)------------------------------
% 1.69/0.61  % (1131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (1131)Termination reason: Refutation
% 1.69/0.61  
% 1.69/0.61  % (1131)Memory used [KB]: 11513
% 1.69/0.61  % (1131)Time elapsed: 0.195 s
% 1.69/0.61  % (1131)------------------------------
% 1.69/0.61  % (1131)------------------------------
% 1.69/0.62  % (1111)Success in time 0.248 s
%------------------------------------------------------------------------------

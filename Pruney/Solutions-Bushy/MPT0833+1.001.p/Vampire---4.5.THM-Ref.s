%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0833+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:43 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 339 expanded)
%              Number of leaves         :   17 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  339 (1397 expanded)
%              Number of equality atoms :   33 ( 103 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f193,f376,f388,f951,f1077])).

fof(f1077,plain,
    ( ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1022,f175])).

fof(f175,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f124,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

fof(f124,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_relset_1(sK0,sK1,X8,X8) ) ),
    inference(resolution,[],[f71,f49])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f1022,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f115,f975])).

fof(f975,plain,
    ( ! [X0] : sK3 = k8_relat_1(X0,sK3)
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(resolution,[],[f192,f492])).

fof(f492,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0,sK3,sK3),sK1)
        | sK3 = k8_relat_1(X0,sK3) )
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f484,f92])).

fof(f92,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f484,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0,sK3,sK3),sK1)
        | sK3 = k8_relat_1(X0,sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_16 ),
    inference(resolution,[],[f442,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X1),sK6(X0,X1,X1)),X1)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X1),sK6(X0,X1,X1)),X1)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(factoring,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK6(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                    & r2_hidden(sK6(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f442,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | r2_hidden(X3,sK1) )
    | ~ spl7_16 ),
    inference(resolution,[],[f375,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f375,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl7_16
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f192,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_8
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f115,plain,(
    ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f114,f49])).

fof(f114,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f51,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f51,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f951,plain,
    ( spl7_7
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f950])).

fof(f950,plain,
    ( $false
    | spl7_7
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f949,f175])).

fof(f949,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK3)
    | spl7_7
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f115,f948])).

fof(f948,plain,
    ( sK3 = k8_relat_1(sK2,sK3)
    | spl7_7
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f947,f92])).

fof(f947,plain,
    ( sK3 = k8_relat_1(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | spl7_7
    | ~ spl7_16 ),
    inference(duplicate_literal_removal,[],[f942])).

fof(f942,plain,
    ( sK3 = k8_relat_1(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | sK3 = k8_relat_1(sK2,sK3)
    | spl7_7
    | ~ spl7_16 ),
    inference(resolution,[],[f775,f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f294,f154])).

fof(f294,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X1),sK6(X0,X1,X1)),X1)
      | ~ r2_hidden(sK6(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X1),sK6(X0,X1,X1)),X1)
      | ~ r2_hidden(sK6(X0,X1,X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f154,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f775,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0,sK3,sK3),sK2)
        | sK3 = k8_relat_1(X0,sK3) )
    | spl7_7
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f774,f189])).

fof(f189,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl7_7
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f774,plain,
    ( ! [X0] :
        ( sK3 = k8_relat_1(X0,sK3)
        | v1_xboole_0(sK2)
        | r2_hidden(sK6(X0,sK3,sK3),sK2) )
    | ~ spl7_16 ),
    inference(resolution,[],[f596,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f596,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(X0,sK3,sK3),sK2)
        | sK3 = k8_relat_1(X0,sK3) )
    | ~ spl7_16 ),
    inference(resolution,[],[f492,f197])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X4)
      | ~ r2_hidden(X3,X5)
      | m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f67,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f388,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f386,f175])).

fof(f386,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f115,f385])).

fof(f385,plain,
    ( ! [X2] : sK3 = k8_relat_1(X2,sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f379,f92])).

fof(f379,plain,
    ( ! [X2] :
        ( sK3 = k8_relat_1(X2,sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f100,f154])).

fof(f100,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_3
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f376,plain,
    ( spl7_4
    | spl7_16 ),
    inference(avatar_split_clause,[],[f112,f374,f102])).

fof(f102,plain,
    ( spl7_4
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f105,f63])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f67,f49])).

fof(f193,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f186,f191,f188])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f97,f50])).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X3)
      | ~ r2_hidden(X4,X5)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f68,f64])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f104,plain,
    ( spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f95,f102,f99])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f68,f49])).

%------------------------------------------------------------------------------

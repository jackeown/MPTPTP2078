%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t191_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:39 EDT 2019

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 327 expanded)
%              Number of leaves         :   10 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  222 (2413 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(global_subsumption,[],[f121,f341])).

fof(f341,plain,(
    r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(resolution,[],[f331,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t191_funct_2.p',d3_tarski)).

fof(f331,plain,(
    r2_hidden(sK5(k2_relat_1(sK3),sK0),sK0) ),
    inference(global_subsumption,[],[f236,f322])).

fof(f322,plain,
    ( r2_hidden(sK5(k2_relat_1(sK3),sK0),sK0)
    | ~ m1_subset_1(sK6(sK5(k2_relat_1(sK3),sK0),sK1,sK3),sK1) ),
    inference(superposition,[],[f69,f317])).

fof(f317,plain,(
    k3_funct_2(sK1,sK2,sK3,sK6(sK5(k2_relat_1(sK3),sK0),sK1,sK3)) = sK5(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f291,f265])).

fof(f265,plain,(
    k1_funct_1(sK3,sK6(sK5(k2_relat_1(sK3),sK0),sK1,sK3)) = sK5(k2_relat_1(sK3),sK0) ),
    inference(resolution,[],[f126,f128])).

fof(f128,plain,(
    r2_hidden(sK5(k2_relat_1(sK3),sK0),k2_relat_1(sK3)) ),
    inference(resolution,[],[f121,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f126,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK6(X1,sK1,sK3)) = X1 ) ),
    inference(global_subsumption,[],[f66,f67,f68,f123])).

fof(f123,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK6(X1,sK1,sK3)) = X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f91,f95])).

fof(f95,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f68,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t191_funct_2.p',redefinition_k2_relset_1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | k1_funct_1(X3,sK6(X0,X1,X3)) = X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK6(X0,X1,X3)) = X0
        & m1_subset_1(sK6(X0,X1,X3),X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f60])).

fof(f60,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
     => ( k1_funct_1(X3,sK6(X0,X1,X3)) = X0
        & m1_subset_1(sK6(X0,X1,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t191_funct_2.p',t190_funct_2)).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                  | ~ m1_subset_1(X4,sK1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
              & v1_funct_2(X3,sK1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(X1,sK2,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK2,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
            & v1_funct_2(X3,X1,sK2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK3),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK3,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t191_funct_2.p',t191_funct_2)).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f291,plain,(
    k3_funct_2(sK1,sK2,sK3,sK6(sK5(k2_relat_1(sK3),sK0),sK1,sK3)) = k1_funct_1(sK3,sK6(sK5(k2_relat_1(sK3),sK0),sK1,sK3)) ),
    inference(resolution,[],[f236,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(global_subsumption,[],[f64,f66,f67,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f68,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t191_funct_2.p',redefinition_k3_funct_2)).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f236,plain,(
    m1_subset_1(sK6(sK5(k2_relat_1(sK3),sK0),sK1,sK3),sK1) ),
    inference(resolution,[],[f125,f128])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | m1_subset_1(sK6(X0,sK1,sK3),sK1) ) ),
    inference(global_subsumption,[],[f66,f67,f68,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | m1_subset_1(sK6(X0,sK1,sK3),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f90,f95])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f121,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f95,f70])).

fof(f70,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------

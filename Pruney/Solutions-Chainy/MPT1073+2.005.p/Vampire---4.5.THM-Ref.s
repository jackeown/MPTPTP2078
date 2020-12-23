%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:56 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 202 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   20
%              Number of atoms          :  248 ( 854 expanded)
%              Number of equality atoms :   30 ( 134 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f67])).

fof(f67,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f66,f63])).

fof(f63,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f66,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f61,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f129,plain,(
    ~ r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f128,f64])).

fof(f64,plain,(
    r2_hidden(sK0,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f41,f62])).

fof(f62,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f122,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK5(X1,k1_relat_1(sK3),sK3),X2)
      | ~ r2_hidden(X1,k2_relat_1(sK3))
      | ~ r1_tarski(k1_relat_1(sK3),X2) ) ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
      | ~ r2_hidden(X0,k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f70,f63])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f50,f65])).

fof(f65,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f122,plain,(
    ~ r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),sK1) ),
    inference(resolution,[],[f104,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f104,plain,(
    ~ m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1) ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1) ),
    inference(superposition,[],[f42,f87])).

fof(f87,plain,(
    sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3)) ),
    inference(resolution,[],[f84,f64])).

fof(f84,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK5(X3,k1_relat_1(sK3),sK3)) = X3 ) ),
    inference(subsumption_resolution,[],[f83,f63])).

fof(f83,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK5(X3,k1_relat_1(sK3),sK3)) = X3
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f81,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK5(X3,k1_relat_1(sK3),sK3)) = X3
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f74,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK5(X1,k1_relat_1(sK3),sK3),X1),sK3)
      | ~ r2_hidden(X1,k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f71,f63])).

fof(f71,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK5(X1,k1_relat_1(sK3),sK3),X1),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f51,f65])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.24/0.55  % (15788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.24/0.55  % (15804)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.24/0.55  % (15805)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.24/0.55  % (15781)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.24/0.56  % (15780)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.24/0.56  % (15797)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.24/0.56  % (15787)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.24/0.56  % (15789)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.24/0.57  % (15779)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.24/0.57  % (15808)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.24/0.57  % (15788)Refutation found. Thanks to Tanya!
% 0.24/0.57  % SZS status Theorem for theBenchmark
% 0.24/0.57  % SZS output start Proof for theBenchmark
% 0.24/0.57  fof(f130,plain,(
% 0.24/0.57    $false),
% 0.24/0.57    inference(subsumption_resolution,[],[f129,f67])).
% 0.24/0.57  fof(f67,plain,(
% 0.24/0.57    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.24/0.57    inference(subsumption_resolution,[],[f66,f63])).
% 0.24/0.57  fof(f63,plain,(
% 0.24/0.57    v1_relat_1(sK3)),
% 0.24/0.57    inference(resolution,[],[f40,f54])).
% 0.24/0.57  fof(f54,plain,(
% 0.24/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f21])).
% 0.24/0.57  fof(f21,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.57    inference(ennf_transformation,[],[f7])).
% 0.24/0.57  fof(f7,axiom,(
% 0.24/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.24/0.57  fof(f40,plain,(
% 0.24/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.24/0.57    inference(cnf_transformation,[],[f27])).
% 0.24/0.57  fof(f27,plain,(
% 0.24/0.57    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.24/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.24/0.57  fof(f26,plain,(
% 0.24/0.57    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.24/0.57    introduced(choice_axiom,[])).
% 0.24/0.57  fof(f15,plain,(
% 0.24/0.57    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.24/0.57    inference(flattening,[],[f14])).
% 0.24/0.57  fof(f14,plain,(
% 0.24/0.57    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.24/0.57    inference(ennf_transformation,[],[f12])).
% 0.24/0.57  fof(f12,plain,(
% 0.24/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.24/0.57    inference(pure_predicate_removal,[],[f11])).
% 0.24/0.57  fof(f11,negated_conjecture,(
% 0.24/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.24/0.57    inference(negated_conjecture,[],[f10])).
% 0.24/0.57  fof(f10,conjecture,(
% 0.24/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.24/0.57  fof(f66,plain,(
% 0.24/0.57    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.24/0.57    inference(resolution,[],[f61,f44])).
% 0.24/0.57  fof(f44,plain,(
% 0.24/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f28])).
% 0.24/0.57  fof(f28,plain,(
% 0.24/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.24/0.57    inference(nnf_transformation,[],[f17])).
% 0.24/0.57  fof(f17,plain,(
% 0.24/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.24/0.57    inference(ennf_transformation,[],[f3])).
% 0.24/0.57  fof(f3,axiom,(
% 0.24/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.24/0.57  fof(f61,plain,(
% 0.24/0.57    v4_relat_1(sK3,sK1)),
% 0.24/0.57    inference(resolution,[],[f40,f56])).
% 0.24/0.57  fof(f56,plain,(
% 0.24/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f23])).
% 0.24/0.57  fof(f23,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.57    inference(ennf_transformation,[],[f13])).
% 0.24/0.57  fof(f13,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.24/0.57    inference(pure_predicate_removal,[],[f8])).
% 0.24/0.57  fof(f8,axiom,(
% 0.24/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.24/0.57  fof(f129,plain,(
% 0.24/0.57    ~r1_tarski(k1_relat_1(sK3),sK1)),
% 0.24/0.57    inference(subsumption_resolution,[],[f128,f64])).
% 0.24/0.57  fof(f64,plain,(
% 0.24/0.57    r2_hidden(sK0,k2_relat_1(sK3))),
% 0.24/0.57    inference(backward_demodulation,[],[f41,f62])).
% 0.24/0.57  fof(f62,plain,(
% 0.24/0.57    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.24/0.57    inference(resolution,[],[f40,f55])).
% 0.24/0.57  fof(f55,plain,(
% 0.24/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f22])).
% 0.24/0.57  fof(f22,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.57    inference(ennf_transformation,[],[f9])).
% 0.24/0.57  fof(f9,axiom,(
% 0.24/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.24/0.57  fof(f41,plain,(
% 0.24/0.57    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.24/0.57    inference(cnf_transformation,[],[f27])).
% 0.24/0.57  fof(f128,plain,(
% 0.24/0.57    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),sK1)),
% 0.24/0.57    inference(resolution,[],[f122,f76])).
% 0.24/0.57  fof(f76,plain,(
% 0.24/0.57    ( ! [X2,X1] : (r2_hidden(sK5(X1,k1_relat_1(sK3),sK3),X2) | ~r2_hidden(X1,k2_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),X2)) )),
% 0.24/0.57    inference(resolution,[],[f73,f47])).
% 0.24/0.57  fof(f47,plain,(
% 0.24/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f32])).
% 0.24/0.57  fof(f32,plain,(
% 0.24/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.24/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.24/0.57  fof(f31,plain,(
% 0.24/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.24/0.57    introduced(choice_axiom,[])).
% 0.24/0.57  fof(f30,plain,(
% 0.24/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.24/0.57    inference(rectify,[],[f29])).
% 0.24/0.57  fof(f29,plain,(
% 0.24/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.24/0.57    inference(nnf_transformation,[],[f19])).
% 0.24/0.57  fof(f19,plain,(
% 0.24/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.24/0.57    inference(ennf_transformation,[],[f1])).
% 0.24/0.57  fof(f1,axiom,(
% 0.24/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.24/0.57  fof(f73,plain,(
% 0.24/0.57    ( ! [X0] : (r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~r2_hidden(X0,k2_relat_1(sK3))) )),
% 0.24/0.57    inference(subsumption_resolution,[],[f70,f63])).
% 0.24/0.57  fof(f70,plain,(
% 0.24/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.24/0.57    inference(superposition,[],[f50,f65])).
% 0.24/0.57  fof(f65,plain,(
% 0.24/0.57    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))),
% 0.24/0.57    inference(resolution,[],[f63,f43])).
% 0.24/0.57  fof(f43,plain,(
% 0.24/0.57    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f16])).
% 0.24/0.57  fof(f16,plain,(
% 0.24/0.57    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.24/0.57    inference(ennf_transformation,[],[f5])).
% 0.24/0.57  fof(f5,axiom,(
% 0.24/0.57    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.24/0.57  fof(f50,plain,(
% 0.24/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f36])).
% 0.24/0.57  fof(f36,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.24/0.57  fof(f35,plain,(
% 0.24/0.57    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 0.24/0.57    introduced(choice_axiom,[])).
% 0.24/0.57  fof(f34,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(rectify,[],[f33])).
% 0.24/0.57  fof(f33,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(nnf_transformation,[],[f20])).
% 0.24/0.57  fof(f20,plain,(
% 0.24/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(ennf_transformation,[],[f4])).
% 0.24/0.57  fof(f4,axiom,(
% 0.24/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.24/0.57  fof(f122,plain,(
% 0.24/0.57    ~r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),sK1)),
% 0.24/0.57    inference(resolution,[],[f104,f46])).
% 0.24/0.57  fof(f46,plain,(
% 0.24/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f18])).
% 0.24/0.57  fof(f18,plain,(
% 0.24/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.24/0.57    inference(ennf_transformation,[],[f2])).
% 0.24/0.57  fof(f2,axiom,(
% 0.24/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.24/0.57  fof(f104,plain,(
% 0.24/0.57    ~m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1)),
% 0.24/0.57    inference(trivial_inequality_removal,[],[f103])).
% 0.24/0.57  fof(f103,plain,(
% 0.24/0.57    sK0 != sK0 | ~m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1)),
% 0.24/0.57    inference(superposition,[],[f42,f87])).
% 0.24/0.57  fof(f87,plain,(
% 0.24/0.57    sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3))),
% 0.24/0.57    inference(resolution,[],[f84,f64])).
% 0.24/0.57  fof(f84,plain,(
% 0.24/0.57    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK3)) | k1_funct_1(sK3,sK5(X3,k1_relat_1(sK3),sK3)) = X3) )),
% 0.24/0.57    inference(subsumption_resolution,[],[f83,f63])).
% 0.24/0.57  fof(f83,plain,(
% 0.24/0.57    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK3)) | k1_funct_1(sK3,sK5(X3,k1_relat_1(sK3),sK3)) = X3 | ~v1_relat_1(sK3)) )),
% 0.24/0.57    inference(subsumption_resolution,[],[f81,f39])).
% 0.24/0.57  fof(f39,plain,(
% 0.24/0.57    v1_funct_1(sK3)),
% 0.24/0.57    inference(cnf_transformation,[],[f27])).
% 0.24/0.57  fof(f81,plain,(
% 0.24/0.57    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK3)) | k1_funct_1(sK3,sK5(X3,k1_relat_1(sK3),sK3)) = X3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.24/0.57    inference(resolution,[],[f74,f58])).
% 0.24/0.57  fof(f58,plain,(
% 0.24/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f38])).
% 0.24/0.57  fof(f38,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(flattening,[],[f37])).
% 0.24/0.57  fof(f37,plain,(
% 0.24/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(nnf_transformation,[],[f25])).
% 0.24/0.57  fof(f25,plain,(
% 0.24/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.24/0.57    inference(flattening,[],[f24])).
% 0.24/0.57  fof(f24,plain,(
% 0.24/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.24/0.57    inference(ennf_transformation,[],[f6])).
% 0.24/0.57  fof(f6,axiom,(
% 0.24/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.24/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.24/0.57  fof(f74,plain,(
% 0.24/0.57    ( ! [X1] : (r2_hidden(k4_tarski(sK5(X1,k1_relat_1(sK3),sK3),X1),sK3) | ~r2_hidden(X1,k2_relat_1(sK3))) )),
% 0.24/0.57    inference(subsumption_resolution,[],[f71,f63])).
% 0.24/0.57  fof(f71,plain,(
% 0.24/0.57    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X1,k1_relat_1(sK3),sK3),X1),sK3) | ~v1_relat_1(sK3)) )),
% 0.24/0.57    inference(superposition,[],[f51,f65])).
% 0.24/0.57  fof(f51,plain,(
% 0.24/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f36])).
% 0.24/0.57  fof(f42,plain,(
% 0.24/0.57    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.24/0.57    inference(cnf_transformation,[],[f27])).
% 0.24/0.57  % SZS output end Proof for theBenchmark
% 0.24/0.57  % (15788)------------------------------
% 0.24/0.57  % (15788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.57  % (15788)Termination reason: Refutation
% 0.24/0.57  
% 0.24/0.57  % (15788)Memory used [KB]: 10746
% 0.24/0.57  % (15788)Time elapsed: 0.168 s
% 0.24/0.57  % (15788)------------------------------
% 0.24/0.57  % (15788)------------------------------
% 0.24/0.57  % (15795)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.24/0.57  % (15774)Success in time 0.198 s
%------------------------------------------------------------------------------

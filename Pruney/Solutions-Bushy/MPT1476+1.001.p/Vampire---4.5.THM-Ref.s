%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:57 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  138 (2009 expanded)
%              Number of leaves         :   18 ( 630 expanded)
%              Depth                    :   40
%              Number of atoms          :  415 (10381 expanded)
%              Number of equality atoms :   67 ( 622 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(subsumption_resolution,[],[f394,f50])).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
      | ~ r1_orders_2(sK0,sK1,sK2) )
    & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
      | r1_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                  | r1_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,X1))
                | ~ r1_orders_2(sK0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,X1))
                | r1_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,X1))
              | ~ r1_orders_2(sK0,X1,X2) )
            & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,X1))
              | r1_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,sK1))
            | ~ r1_orders_2(sK0,sK1,X2) )
          & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,sK1))
            | r1_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,sK1))
          | ~ r1_orders_2(sK0,sK1,X2) )
        & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,sK1))
          | r1_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
        | ~ r1_orders_2(sK0,sK1,sK2) )
      & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
        | r1_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <~> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_lattice3)).

fof(f394,plain,(
    ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f391,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f391,plain,(
    ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f390,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f390,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(forward_demodulation,[],[f389,f251])).

fof(f251,plain,(
    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(superposition,[],[f247,f135])).

fof(f135,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) ),
    inference(backward_demodulation,[],[f131,f133])).

fof(f133,plain,(
    k4_relat_1(u1_orders_2(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(resolution,[],[f117,f50])).

fof(f117,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = k4_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f131,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f62,f50])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(f247,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
      | u1_struct_0(k7_lattice3(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f245,f109])).

fof(f109,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(resolution,[],[f92,f50])).

fof(f92,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) ) ),
    inference(subsumption_resolution,[],[f91,f64])).

fof(f91,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f65,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f245,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
      | u1_struct_0(k7_lattice3(sK0)) = X0 ) ),
    inference(resolution,[],[f169,f50])).

fof(f169,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_orders_2(X2)
      | g1_orders_2(u1_struct_0(k7_lattice3(X2)),u1_orders_2(k7_lattice3(X2))) != g1_orders_2(X3,X4)
      | u1_struct_0(k7_lattice3(X2)) = X3 ) ),
    inference(resolution,[],[f164,f64])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f389,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f388,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f388,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(forward_demodulation,[],[f387,f251])).

fof(f387,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f384,f371])).

fof(f371,plain,(
    ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f99,f370])).

fof(f370,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f369,f50])).

fof(f369,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f368,f51])).

fof(f368,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f367,f52])).

fof(f367,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f315,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f315,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f207,f306])).

fof(f306,plain,(
    u1_orders_2(sK0) = k4_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    inference(backward_demodulation,[],[f87,f305])).

fof(f305,plain,(
    k4_relat_1(u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f304])).

fof(f304,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | k4_relat_1(u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
    inference(superposition,[],[f278,f135])).

fof(f278,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
      | u1_orders_2(k7_lattice3(sK0)) = X1 ) ),
    inference(forward_demodulation,[],[f275,f252])).

fof(f252,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) ),
    inference(backward_demodulation,[],[f109,f251])).

fof(f275,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
      | u1_orders_2(k7_lattice3(sK0)) = X1 ) ),
    inference(resolution,[],[f272,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f272,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f271,f50])).

fof(f271,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f259,f64])).

fof(f259,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f61,f251])).

fof(f87,plain,(
    u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0))) ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,(
    ! [X1] :
      ( ~ l1_orders_2(X1)
      | u1_orders_2(X1) = k4_relat_1(k4_relat_1(u1_orders_2(X1))) ) ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f84,plain,(
    ! [X0] :
      ( v1_relat_1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f61,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f207,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f206,f50])).

fof(f206,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f205,f64])).

fof(f205,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0)))) ),
    inference(resolution,[],[f202,f84])).

fof(f202,plain,
    ( ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f201,f79])).

fof(f79,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f77,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f201,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f200,f50])).

fof(f200,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f199,f64])).

fof(f199,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f198,f116])).

fof(f116,plain,(
    m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,
    ( m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f112,f52])).

fof(f112,plain,
    ( m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f73,f96])).

fof(f96,plain,(
    sK2 = k8_lattice3(sK0,sK2) ),
    inference(resolution,[],[f93,f52])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k8_lattice3(sK0,X0) = X0 ) ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k8_lattice3(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattice3)).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_lattice3)).

fof(f198,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f197,f114])).

fof(f114,plain,(
    m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,
    ( m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f111,plain,
    ( m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f73,f95])).

fof(f95,plain,(
    sK1 = k8_lattice3(sK0,sK1) ),
    inference(resolution,[],[f93,f51])).

fof(f197,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f67,f100])).

fof(f100,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f97,f96])).

fof(f97,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),sK1)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f53,f95])).

fof(f53,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    inference(backward_demodulation,[],[f98,f96])).

fof(f98,plain,
    ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f54,f95])).

fof(f54,plain,
    ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f384,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f380,f68])).

fof(f380,plain,(
    r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0))) ),
    inference(forward_demodulation,[],[f379,f305])).

fof(f379,plain,(
    r2_hidden(k4_tarski(sK2,sK1),k4_relat_1(u1_orders_2(sK0))) ),
    inference(subsumption_resolution,[],[f377,f320])).

fof(f320,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f307,f274])).

fof(f274,plain,(
    v1_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    inference(resolution,[],[f272,f75])).

fof(f307,plain,
    ( ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | v1_relat_1(u1_orders_2(sK0)) ),
    inference(backward_demodulation,[],[f89,f305])).

fof(f89,plain,
    ( ~ v1_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | v1_relat_1(u1_orders_2(sK0)) ),
    inference(superposition,[],[f55,f87])).

fof(f377,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k4_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f375,f79])).

fof(f375,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f374,f50])).

fof(f374,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f373,f51])).

fof(f373,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f372,f52])).

fof(f372,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f370,f67])).

%------------------------------------------------------------------------------

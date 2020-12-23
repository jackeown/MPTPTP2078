%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 (1324 expanded)
%              Number of leaves         :   16 ( 458 expanded)
%              Depth                    :   32
%              Number of atoms          :  384 (9456 expanded)
%              Number of equality atoms :  100 ( 712 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(subsumption_resolution,[],[f245,f97])).

fof(f97,plain,(
    ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f94,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f44,f92,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f92,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f43,f82])).

fof(f82,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                | ~ m1_subset_1(X4,sK1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
            & v1_funct_2(X3,sK1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
            | ~ m1_subset_1(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
          | ~ m1_subset_1(X4,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f43,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f245,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f91,f237])).

fof(f237,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f236,f210])).

fof(f210,plain,
    ( r2_hidden(sK4(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK4(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f206,f137])).

fof(f137,plain,(
    ! [X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | r2_hidden(sK4(sK1,X1,sK3),sK1)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f136,f80])).

fof(f80,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1,sK3),sK1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f133,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1,sK3),sK1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f72,f129])).

fof(f129,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f93,f81])).

fof(f81,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f93,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f72,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f206,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f205,f95])).

fof(f95,plain,(
    ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f92,f46])).

fof(f205,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f51,f203])).

fof(f203,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f202,f160])).

fof(f160,plain,(
    ! [X4] :
      ( r2_hidden(sK4(sK1,X4,sK3),sK1)
      | k1_xboole_0 = sK2
      | k2_relat_1(sK3) = k2_relset_1(sK1,X4,sK3) ) ),
    inference(resolution,[],[f137,f50])).

fof(f202,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2
    | ~ r2_hidden(sK4(sK1,sK0,sK3),sK1) ),
    inference(resolution,[],[f201,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f201,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f200,f50])).

fof(f200,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f196,f170])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f140,f129])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    inference(resolution,[],[f79,f80])).

fof(f79,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK3)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4)))
      | ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X4,sK3)),X4) ) ),
    inference(resolution,[],[f39,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f196,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)
      | ~ m1_subset_1(sK4(sK1,X0,sK3),sK1)
      | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f42,f175])).

fof(f175,plain,(
    ! [X0] :
      ( k3_funct_2(sK1,sK2,sK3,sK4(sK1,X0,sK3)) = k1_funct_1(sK3,sK4(sK1,X0,sK3))
      | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f160,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f149,f45])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f148,f37])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f145,f40])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f77,f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | ~ v1_funct_2(sK3,X1,X2)
      | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f39,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f42,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f236,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_hidden(sK4(sK1,sK0,sK3),sK1) ),
    inference(resolution,[],[f235,f45])).

fof(f235,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f234,f206])).

fof(f234,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f225,f170])).

fof(f225,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f42,f213])).

fof(f213,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK4(sK1,sK0,sK3)) = k1_funct_1(sK3,sK4(sK1,sK0,sK3))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k3_funct_2(sK1,sK2,sK3,sK4(sK1,sK0,sK3)) = k1_funct_1(sK3,sK4(sK1,sK0,sK3)) ),
    inference(resolution,[],[f208,f169])).

fof(f169,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(sK1,X0))
      | k1_xboole_0 = sK2
      | k3_funct_2(sK1,sK2,sK3,sK4(sK1,X0,sK3)) = k1_funct_1(sK3,sK4(sK1,X0,sK3)) ) ),
    inference(resolution,[],[f164,f154])).

fof(f164,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK1,X7,sK3),sK1)
      | k1_xboole_0 = sK2
      | r1_tarski(sK3,k2_zfmisc_1(sK1,X7)) ) ),
    inference(resolution,[],[f137,f46])).

fof(f208,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f206,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(backward_demodulation,[],[f83,f82])).

fof(f83,plain,(
    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (12161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (12163)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (12155)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (12160)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.48  % (12169)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.48  % (12158)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.48  % (12159)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.48  % (12150)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (12153)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.49  % (12149)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (12151)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.49  % (12152)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (12154)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (12160)Refutation not found, incomplete strategy% (12160)------------------------------
% 0.19/0.50  % (12160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (12160)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (12160)Memory used [KB]: 10618
% 0.19/0.50  % (12160)Time elapsed: 0.087 s
% 0.19/0.50  % (12160)------------------------------
% 0.19/0.50  % (12160)------------------------------
% 0.19/0.50  % (12156)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.50  % (12164)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.50  % (12165)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.50  % (12162)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.50  % (12164)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f260,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f245,f97])).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f94,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f44,f92,f64])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.50    inference(flattening,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    ~r1_tarski(k2_relat_1(sK3),sK0)),
% 0.19/0.50    inference(backward_demodulation,[],[f43,f82])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f41,f50])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f31,f30,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.19/0.50    inference(flattening,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.19/0.50    inference(negated_conjecture,[],[f12])).
% 0.19/0.50  fof(f12,conjecture,(
% 0.19/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.50  fof(f245,plain,(
% 0.19/0.50    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.50    inference(backward_demodulation,[],[f91,f237])).
% 0.19/0.50  fof(f237,plain,(
% 0.19/0.50    k1_xboole_0 = sK2),
% 0.19/0.50    inference(subsumption_resolution,[],[f236,f210])).
% 0.19/0.50  fof(f210,plain,(
% 0.19/0.50    r2_hidden(sK4(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f207])).
% 0.19/0.50  fof(f207,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | r2_hidden(sK4(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(resolution,[],[f206,f137])).
% 0.19/0.50  fof(f137,plain,(
% 0.19/0.50    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | r2_hidden(sK4(sK1,X1,sK3),sK1) | k1_xboole_0 = sK2) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f136,f80])).
% 0.19/0.50  fof(f80,plain,(
% 0.19/0.50    v1_relat_1(sK3)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f41,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    ( ! [X1] : (r2_hidden(sK4(sK1,X1,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f133,f39])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    v1_funct_1(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    ( ! [X1] : (r2_hidden(sK4(sK1,X1,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 0.19/0.50    inference(superposition,[],[f72,f129])).
% 0.19/0.50  fof(f129,plain,(
% 0.19/0.50    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(superposition,[],[f93,f81])).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f41,f49])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(subsumption_resolution,[],[f85,f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    v1_funct_2(sK3,sK1,sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.19/0.50    inference(resolution,[],[f41,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(flattening,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.50    inference(equality_resolution,[],[f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.50    inference(flattening,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.19/0.50  fof(f206,plain,(
% 0.19/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(subsumption_resolution,[],[f205,f95])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f92,f46])).
% 0.19/0.50  fof(f205,plain,(
% 0.19/0.50    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(superposition,[],[f51,f203])).
% 0.19/0.50  fof(f203,plain,(
% 0.19/0.50    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(subsumption_resolution,[],[f202,f160])).
% 0.19/0.50  fof(f160,plain,(
% 0.19/0.50    ( ! [X4] : (r2_hidden(sK4(sK1,X4,sK3),sK1) | k1_xboole_0 = sK2 | k2_relat_1(sK3) = k2_relset_1(sK1,X4,sK3)) )),
% 0.19/0.50    inference(resolution,[],[f137,f50])).
% 0.19/0.50  fof(f202,plain,(
% 0.19/0.50    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2 | ~r2_hidden(sK4(sK1,sK0,sK3),sK1)),
% 0.19/0.50    inference(resolution,[],[f201,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.50  fof(f201,plain,(
% 0.19/0.50    ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(subsumption_resolution,[],[f200,f50])).
% 0.19/0.50  fof(f200,plain,(
% 0.19/0.50    ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f197])).
% 0.19/0.50  fof(f197,plain,(
% 0.19/0.50    ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(resolution,[],[f196,f170])).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = sK2) )),
% 0.19/0.50    inference(superposition,[],[f140,f129])).
% 0.19/0.50  fof(f140,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) )),
% 0.19/0.50    inference(resolution,[],[f79,f80])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    ( ! [X4] : (~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4))) | ~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X4,sK3)),X4)) )),
% 0.19/0.50    inference(resolution,[],[f39,f71])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_relat_1(X2)) )),
% 0.19/0.50    inference(equality_resolution,[],[f63])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f36])).
% 0.19/0.50  fof(f196,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) | ~m1_subset_1(sK4(sK1,X0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3) | k1_xboole_0 = sK2) )),
% 0.19/0.50    inference(superposition,[],[f42,f175])).
% 0.19/0.50  fof(f175,plain,(
% 0.19/0.50    ( ! [X0] : (k3_funct_2(sK1,sK2,sK3,sK4(sK1,X0,sK3)) = k1_funct_1(sK3,sK4(sK1,X0,sK3)) | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3) | k1_xboole_0 = sK2) )),
% 0.19/0.50    inference(resolution,[],[f160,f154])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.19/0.50    inference(resolution,[],[f149,f45])).
% 0.19/0.50  fof(f149,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f148,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ~v1_xboole_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f148,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f145,f40])).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) )),
% 0.19/0.50    inference(resolution,[],[f77,f41])).
% 0.19/0.50  fof(f77,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK3,X1,X2) | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(resolution,[],[f39,f65])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.19/0.50    inference(flattening,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.19/0.50  fof(f236,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | ~r2_hidden(sK4(sK1,sK0,sK3),sK1)),
% 0.19/0.50    inference(resolution,[],[f235,f45])).
% 0.19/0.50  fof(f235,plain,(
% 0.19/0.50    ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(subsumption_resolution,[],[f234,f206])).
% 0.19/0.50  fof(f234,plain,(
% 0.19/0.50    ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f231])).
% 0.19/0.50  fof(f231,plain,(
% 0.19/0.50    ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(resolution,[],[f225,f170])).
% 0.19/0.50  fof(f225,plain,(
% 0.19/0.50    r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) | ~m1_subset_1(sK4(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(superposition,[],[f42,f213])).
% 0.19/0.50  fof(f213,plain,(
% 0.19/0.50    k3_funct_2(sK1,sK2,sK3,sK4(sK1,sK0,sK3)) = k1_funct_1(sK3,sK4(sK1,sK0,sK3)) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f212])).
% 0.19/0.50  fof(f212,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k3_funct_2(sK1,sK2,sK3,sK4(sK1,sK0,sK3)) = k1_funct_1(sK3,sK4(sK1,sK0,sK3))),
% 0.19/0.50    inference(resolution,[],[f208,f169])).
% 0.19/0.50  fof(f169,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) | k1_xboole_0 = sK2 | k3_funct_2(sK1,sK2,sK3,sK4(sK1,X0,sK3)) = k1_funct_1(sK3,sK4(sK1,X0,sK3))) )),
% 0.19/0.50    inference(resolution,[],[f164,f154])).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    ( ! [X7] : (r2_hidden(sK4(sK1,X7,sK3),sK1) | k1_xboole_0 = sK2 | r1_tarski(sK3,k2_zfmisc_1(sK1,X7))) )),
% 0.19/0.50    inference(resolution,[],[f137,f46])).
% 0.19/0.50  fof(f208,plain,(
% 0.19/0.50    ~r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) | k1_xboole_0 = sK2),
% 0.19/0.50    inference(resolution,[],[f206,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f83,f82])).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f41,f51])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (12164)------------------------------
% 0.19/0.50  % (12164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (12164)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (12164)Memory used [KB]: 6268
% 0.19/0.50  % (12164)Time elapsed: 0.097 s
% 0.19/0.50  % (12164)------------------------------
% 0.19/0.50  % (12164)------------------------------
% 0.19/0.50  % (12157)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.51  % (12166)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.52  % (12167)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.52  % (12168)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.52  % (12148)Success in time 0.165 s
%------------------------------------------------------------------------------

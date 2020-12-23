%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:09 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 233 expanded)
%              Number of leaves         :    9 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  221 (1749 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f28])).

fof(f28,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f16,plain,
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f56,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f54,plain,
    ( ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)
    | ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f39,f52])).

fof(f52,plain,(
    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k3_funct_2(sK1,sK2,sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3)) ),
    inference(forward_demodulation,[],[f51,f44])).

fof(f44,plain,(
    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3)) ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | sK4(k2_relset_1(sK1,sK2,sK3),X0) = k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),X0),sK1,sK3)) ) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
      | k1_funct_1(sK3,sK5(X0,sK1,sK3)) = X0 ) ),
    inference(subsumption_resolution,[],[f41,f25])).

fof(f25,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | k1_funct_1(sK3,sK5(X0,sK1,sK3)) = X0 ) ),
    inference(resolution,[],[f40,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,sK3))
      | ~ v1_funct_2(sK3,X1,X2)
      | k1_funct_1(sK3,sK5(X0,X1,sK3)) = X0 ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | k1_funct_1(X3,sK5(X0,X1,X3)) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK5(X0,X1,X3)) = X0
        & m1_subset_1(sK5(X0,X1,X3),X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f20])).

fof(f20,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
     => ( k1_funct_1(X3,sK5(X0,X1,X3)) = X0
        & m1_subset_1(sK5(X0,X1,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f51,plain,(
    k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3)) ),
    inference(resolution,[],[f50,f28])).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),X0),sK1,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),X0),sK1,sK3)) ) ),
    inference(resolution,[],[f49,f29])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
      | k3_funct_2(sK1,sK2,sK3,sK5(X0,sK1,sK3)) = k1_funct_1(sK3,sK5(X0,sK1,sK3)) ) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0,sK1,sK3),sK1)
      | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f37,f25])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | m1_subset_1(sK5(X0,sK1,sK3),sK1) ) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,sK3))
      | ~ v1_funct_2(sK3,X1,X2)
      | m1_subset_1(sK5(X0,X1,sK3),X1) ) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | m1_subset_1(sK5(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f46,f25])).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | ~ v1_funct_2(sK3,X1,X2)
      | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f33,f24])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,sK5(X0,sK1,sK3)),sK0)
      | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (797671425)
% 0.14/0.37  ipcrm: permission denied for id (797704195)
% 0.14/0.38  ipcrm: permission denied for id (797769737)
% 0.14/0.38  ipcrm: permission denied for id (797835277)
% 0.21/0.39  ipcrm: permission denied for id (797868055)
% 0.21/0.40  ipcrm: permission denied for id (797900829)
% 0.21/0.41  ipcrm: permission denied for id (797999141)
% 0.21/0.42  ipcrm: permission denied for id (798064682)
% 0.21/0.43  ipcrm: permission denied for id (798162997)
% 0.21/0.44  ipcrm: permission denied for id (798195768)
% 0.21/0.46  ipcrm: permission denied for id (798261322)
% 0.21/0.47  ipcrm: permission denied for id (798326863)
% 0.21/0.47  ipcrm: permission denied for id (798359633)
% 0.21/0.47  ipcrm: permission denied for id (798392405)
% 0.21/0.48  ipcrm: permission denied for id (798457946)
% 0.21/0.48  ipcrm: permission denied for id (798490715)
% 0.21/0.49  ipcrm: permission denied for id (798523487)
% 0.21/0.49  ipcrm: permission denied for id (798556257)
% 0.21/0.51  ipcrm: permission denied for id (798720115)
% 0.21/0.51  ipcrm: permission denied for id (798752884)
% 0.21/0.52  ipcrm: permission denied for id (798851191)
% 0.38/0.67  % (7998)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.38/0.67  % (8002)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.38/0.67  % (7998)Refutation found. Thanks to Tanya!
% 0.38/0.67  % SZS status Theorem for theBenchmark
% 0.38/0.67  % SZS output start Proof for theBenchmark
% 0.38/0.67  fof(f57,plain,(
% 0.38/0.67    $false),
% 0.38/0.67    inference(subsumption_resolution,[],[f56,f28])).
% 0.38/0.67  fof(f28,plain,(
% 0.38/0.67    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f17,plain,(
% 0.38/0.67    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.38/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15,f14])).
% 0.38/0.67  fof(f14,plain,(
% 0.38/0.67    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f15,plain,(
% 0.38/0.67    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f16,plain,(
% 0.38/0.67    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f8,plain,(
% 0.38/0.67    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.38/0.67    inference(flattening,[],[f7])).
% 0.38/0.67  fof(f7,plain,(
% 0.38/0.67    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.38/0.67    inference(ennf_transformation,[],[f5])).
% 0.38/0.67  fof(f5,negated_conjecture,(
% 0.38/0.67    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.38/0.67    inference(negated_conjecture,[],[f4])).
% 0.38/0.67  fof(f4,conjecture,(
% 0.38/0.67    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.38/0.67  fof(f56,plain,(
% 0.38/0.67    r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.38/0.67    inference(resolution,[],[f55,f29])).
% 0.38/0.67  fof(f29,plain,(
% 0.38/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f19,plain,(
% 0.38/0.67    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.38/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).
% 0.38/0.67  fof(f18,plain,(
% 0.38/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f9,plain,(
% 0.38/0.67    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f6])).
% 0.38/0.67  fof(f6,plain,(
% 0.38/0.67    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.38/0.67    inference(unused_predicate_definition_removal,[],[f1])).
% 0.38/0.67  fof(f1,axiom,(
% 0.38/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.38/0.67  fof(f55,plain,(
% 0.38/0.67    ~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3))),
% 0.38/0.67    inference(subsumption_resolution,[],[f54,f28])).
% 0.38/0.67  fof(f54,plain,(
% 0.38/0.67    ~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3)) | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.38/0.67    inference(resolution,[],[f53,f30])).
% 0.38/0.67  fof(f30,plain,(
% 0.38/0.67    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f53,plain,(
% 0.38/0.67    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) | ~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3))),
% 0.38/0.67    inference(superposition,[],[f39,f52])).
% 0.38/0.67  fof(f52,plain,(
% 0.38/0.67    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k3_funct_2(sK1,sK2,sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3))),
% 0.38/0.67    inference(forward_demodulation,[],[f51,f44])).
% 0.38/0.67  fof(f44,plain,(
% 0.38/0.67    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3))),
% 0.38/0.67    inference(resolution,[],[f43,f28])).
% 0.38/0.67  fof(f43,plain,(
% 0.38/0.67    ( ! [X0] : (r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | sK4(k2_relset_1(sK1,sK2,sK3),X0) = k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),X0),sK1,sK3))) )),
% 0.38/0.67    inference(resolution,[],[f42,f29])).
% 0.38/0.67  fof(f42,plain,(
% 0.38/0.67    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | k1_funct_1(sK3,sK5(X0,sK1,sK3)) = X0) )),
% 0.38/0.67    inference(subsumption_resolution,[],[f41,f25])).
% 0.38/0.67  fof(f25,plain,(
% 0.38/0.67    v1_funct_2(sK3,sK1,sK2)),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f41,plain,(
% 0.38/0.67    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK2) | k1_funct_1(sK3,sK5(X0,sK1,sK3)) = X0) )),
% 0.38/0.67    inference(resolution,[],[f40,f26])).
% 0.38/0.67  fof(f26,plain,(
% 0.38/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f40,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k2_relset_1(X1,X2,sK3)) | ~v1_funct_2(sK3,X1,X2) | k1_funct_1(sK3,sK5(X0,X1,sK3)) = X0) )),
% 0.38/0.67    inference(resolution,[],[f32,f24])).
% 0.38/0.67  fof(f24,plain,(
% 0.38/0.67    v1_funct_1(sK3)),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f32,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r2_hidden(X0,k2_relset_1(X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | k1_funct_1(X3,sK5(X0,X1,X3)) = X0) )),
% 0.38/0.67    inference(cnf_transformation,[],[f21])).
% 0.38/0.67  fof(f21,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((k1_funct_1(X3,sK5(X0,X1,X3)) = X0 & m1_subset_1(sK5(X0,X1,X3),X1)) | ~r2_hidden(X0,k2_relset_1(X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))),
% 0.38/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f20])).
% 0.38/0.67  fof(f20,plain,(
% 0.38/0.67    ! [X3,X1,X0] : (? [X4] : (k1_funct_1(X3,X4) = X0 & m1_subset_1(X4,X1)) => (k1_funct_1(X3,sK5(X0,X1,X3)) = X0 & m1_subset_1(sK5(X0,X1,X3),X1)))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f11,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(X3,X4) = X0 & m1_subset_1(X4,X1)) | ~r2_hidden(X0,k2_relset_1(X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))),
% 0.38/0.67    inference(flattening,[],[f10])).
% 0.38/0.67  fof(f10,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((? [X4] : (k1_funct_1(X3,X4) = X0 & m1_subset_1(X4,X1)) | ~r2_hidden(X0,k2_relset_1(X1,X2,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)))),
% 0.38/0.67    inference(ennf_transformation,[],[f3])).
% 0.38/0.67  fof(f3,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.38/0.67  fof(f51,plain,(
% 0.38/0.67    k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK1,sK3))),
% 0.38/0.67    inference(resolution,[],[f50,f28])).
% 0.38/0.67  fof(f50,plain,(
% 0.38/0.67    ( ! [X0] : (r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | k1_funct_1(sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),X0),sK1,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK4(k2_relset_1(sK1,sK2,sK3),X0),sK1,sK3))) )),
% 0.38/0.67    inference(resolution,[],[f49,f29])).
% 0.38/0.67  fof(f49,plain,(
% 0.38/0.67    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | k3_funct_2(sK1,sK2,sK3,sK5(X0,sK1,sK3)) = k1_funct_1(sK3,sK5(X0,sK1,sK3))) )),
% 0.38/0.67    inference(resolution,[],[f48,f38])).
% 0.38/0.67  fof(f38,plain,(
% 0.38/0.67    ( ! [X0] : (m1_subset_1(sK5(X0,sK1,sK3),sK1) | ~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))) )),
% 0.38/0.67    inference(subsumption_resolution,[],[f37,f25])).
% 0.38/0.67  fof(f37,plain,(
% 0.38/0.67    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK2) | m1_subset_1(sK5(X0,sK1,sK3),sK1)) )),
% 0.38/0.67    inference(resolution,[],[f36,f26])).
% 0.38/0.67  fof(f36,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k2_relset_1(X1,X2,sK3)) | ~v1_funct_2(sK3,X1,X2) | m1_subset_1(sK5(X0,X1,sK3),X1)) )),
% 0.38/0.67    inference(resolution,[],[f31,f24])).
% 0.38/0.67  fof(f31,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r2_hidden(X0,k2_relset_1(X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | m1_subset_1(sK5(X0,X1,X3),X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f21])).
% 0.38/0.67  fof(f48,plain,(
% 0.38/0.67    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.38/0.67    inference(subsumption_resolution,[],[f47,f22])).
% 0.38/0.67  fof(f22,plain,(
% 0.38/0.67    ~v1_xboole_0(sK1)),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f47,plain,(
% 0.38/0.67    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) )),
% 0.38/0.67    inference(subsumption_resolution,[],[f46,f25])).
% 0.38/0.67  fof(f46,plain,(
% 0.38/0.67    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) )),
% 0.38/0.67    inference(resolution,[],[f45,f26])).
% 0.38/0.67  fof(f45,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK3,X1,X2) | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(X1)) )),
% 0.38/0.67    inference(resolution,[],[f33,f24])).
% 0.38/0.67  fof(f33,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f13])).
% 0.38/0.67  fof(f13,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.38/0.67    inference(flattening,[],[f12])).
% 0.38/0.67  fof(f12,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f2])).
% 0.38/0.67  fof(f2,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.38/0.67  fof(f39,plain,(
% 0.38/0.67    ( ! [X0] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,sK5(X0,sK1,sK3)),sK0) | ~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))) )),
% 0.38/0.67    inference(resolution,[],[f38,f27])).
% 0.38/0.67  fof(f27,plain,(
% 0.38/0.67    ( ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  % SZS output end Proof for theBenchmark
% 0.38/0.67  % (7998)------------------------------
% 0.38/0.67  % (7998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.67  % (7998)Termination reason: Refutation
% 0.38/0.67  
% 0.38/0.67  % (7998)Memory used [KB]: 6268
% 0.38/0.67  % (7998)Time elapsed: 0.091 s
% 0.38/0.67  % (7998)------------------------------
% 0.38/0.67  % (7998)------------------------------
% 0.38/0.67  % (7767)Success in time 0.315 s
%------------------------------------------------------------------------------

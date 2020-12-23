%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 865 expanded)
%              Number of leaves         :   11 ( 298 expanded)
%              Depth                    :   20
%              Number of atoms          :  294 (6049 expanded)
%              Number of equality atoms :   15 (  84 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(subsumption_resolution,[],[f310,f306])).

fof(f306,plain,(
    r2_hidden(sK4(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f293,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f293,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r2_hidden(sK4(sK0,sK0),sK0) ),
    inference(resolution,[],[f290,f165])).

fof(f165,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),X1),X1)
      | r2_hidden(sK4(X1,sK0),X1) ) ),
    inference(resolution,[],[f158,f36])).

fof(f158,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),X2),X2) ) ),
    inference(resolution,[],[f145,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f92,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ~ r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) ),
    inference(resolution,[],[f34,f37])).

fof(f34,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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

% (6245)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f19,plain,
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f92,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) ) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3)) ),
    inference(resolution,[],[f34,f36])).

fof(f290,plain,(
    ! [X2] :
      ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X2)
      | ~ r1_tarski(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f289,f288])).

fof(f288,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK4(sK1,sK1),sK1) ) ),
    inference(resolution,[],[f264,f36])).

fof(f264,plain,(
    ! [X20] :
      ( ~ r1_tarski(sK1,sK1)
      | r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X20)
      | ~ r1_tarski(sK0,X20) ) ),
    inference(forward_demodulation,[],[f261,f98])).

fof(f98,plain,(
    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) ),
    inference(subsumption_resolution,[],[f97,f30])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,
    ( sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f96,f31])).

fof(f31,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,
    ( sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f90,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,
    ( sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK5(X0,X2,X3)) = X2
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK5(X0,X2,X3)) = X2
        & r2_hidden(sK5(X0,X2,X3),X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f26])).

fof(f26,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X3,sK5(X0,X2,X3)) = X2
        & r2_hidden(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

% (6256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f261,plain,(
    ! [X20] :
      ( ~ r1_tarski(sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)),X20)
      | ~ r1_tarski(sK0,X20) ) ),
    inference(resolution,[],[f247,f86])).

% (6236)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f86,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,sK1)
      | r2_hidden(k1_funct_1(sK3,X2),X3)
      | ~ r1_tarski(sK0,X3) ) ),
    inference(resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f83,f28])).

fof(f28,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f33,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f247,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f106,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),X0) ) ),
    inference(resolution,[],[f95,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f95,plain,(
    r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f94,plain,
    ( r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f93,plain,
    ( r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f89,plain,
    ( r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X2,X3),X0)
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f289,plain,(
    ! [X2] :
      ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X2)
      | ~ r1_tarski(sK0,X2)
      | ~ r2_hidden(sK4(sK1,sK1),sK1) ) ),
    inference(resolution,[],[f264,f37])).

fof(f310,plain,(
    ~ r2_hidden(sK4(sK0,sK0),sK0) ),
    inference(resolution,[],[f307,f37])).

fof(f307,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f294,f34])).

fof(f294,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f290,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6244)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (6249)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (6235)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (6230)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (6223)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (6239)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6224)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (6228)Refutation not found, incomplete strategy% (6228)------------------------------
% 0.21/0.53  % (6228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6228)Memory used [KB]: 6268
% 0.21/0.53  % (6228)Time elapsed: 0.124 s
% 0.21/0.53  % (6228)------------------------------
% 0.21/0.53  % (6228)------------------------------
% 0.21/0.53  % (6226)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (6254)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (6227)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (6231)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (6247)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (6249)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f310,f306])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    r2_hidden(sK4(sK0,sK0),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f293,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK0) | r2_hidden(sK4(sK0,sK0),sK0)),
% 0.21/0.54    inference(resolution,[],[f290,f165])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),X1),X1) | r2_hidden(sK4(X1,sK0),X1)) )),
% 0.21/0.54    inference(resolution,[],[f158,f36])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_tarski(X2,sK0) | ~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),X2),X2)) )),
% 0.21/0.54    inference(resolution,[],[f145,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f92,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X0) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f69,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ~r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)),
% 0.21/0.54    inference(resolution,[],[f34,f37])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (6245)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)) )),
% 0.21/0.54    inference(resolution,[],[f68,f35])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.54    inference(resolution,[],[f34,f36])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X2) | ~r1_tarski(sK0,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f289,f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X1) | ~r1_tarski(sK0,X1) | r2_hidden(sK4(sK1,sK1),sK1)) )),
% 0.21/0.54    inference(resolution,[],[f264,f36])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    ( ! [X20] : (~r1_tarski(sK1,sK1) | r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X20) | ~r1_tarski(sK0,X20)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f261,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f97,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f96,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f68,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_funct_1(X3,sK5(X0,X2,X3)) = X2 | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_funct_1(X3,sK5(X0,X2,X3)) = X2 & r2_hidden(sK5(X0,X2,X3),X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) => (k1_funct_1(X3,sK5(X0,X2,X3)) = X2 & r2_hidden(sK5(X0,X2,X3),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (6256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    ( ! [X20] : (~r1_tarski(sK1,sK1) | r2_hidden(k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)),X20) | ~r1_tarski(sK0,X20)) )),
% 0.21/0.54    inference(resolution,[],[f247,f86])).
% 0.21/0.54  % (6236)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,sK1) | r2_hidden(k1_funct_1(sK3,X2),X3) | ~r1_tarski(sK0,X3)) )),
% 0.21/0.54    inference(resolution,[],[f84,f35])).
% 1.43/0.54  fof(f84,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f83,f28])).
% 1.43/0.54  fof(f28,plain,(
% 1.43/0.54    ~v1_xboole_0(sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f20])).
% 1.43/0.54  fof(f83,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f82,f30])).
% 1.43/0.54  fof(f82,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f81,f31])).
% 1.43/0.54  fof(f81,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f80,f32])).
% 1.43/0.54  fof(f80,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)) )),
% 1.43/0.54    inference(duplicate_literal_removal,[],[f79])).
% 1.43/0.54  fof(f79,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)) )),
% 1.43/0.54    inference(superposition,[],[f33,f41])).
% 1.43/0.54  fof(f41,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f14])).
% 1.43/0.54  fof(f14,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.43/0.54    inference(flattening,[],[f13])).
% 1.43/0.54  fof(f13,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f4])).
% 1.43/0.54  fof(f4,axiom,(
% 1.43/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f20])).
% 1.43/0.54  fof(f247,plain,(
% 1.43/0.54    ( ! [X0] : (m1_subset_1(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),X0) | ~r1_tarski(sK1,X0)) )),
% 1.43/0.54    inference(resolution,[],[f106,f39])).
% 1.43/0.54  fof(f39,plain,(
% 1.43/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f25])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.43/0.54    inference(nnf_transformation,[],[f2])).
% 1.43/0.54  fof(f2,axiom,(
% 1.43/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.43/0.54  fof(f106,plain,(
% 1.43/0.54    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),X0)) )),
% 1.43/0.54    inference(resolution,[],[f95,f40])).
% 1.43/0.54  fof(f40,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f12])).
% 1.43/0.54  fof(f12,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.43/0.54    inference(flattening,[],[f11])).
% 1.43/0.54  fof(f11,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.43/0.54    inference(ennf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.43/0.54  fof(f95,plain,(
% 1.43/0.54    r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)),
% 1.43/0.54    inference(subsumption_resolution,[],[f94,f30])).
% 1.43/0.54  fof(f94,plain,(
% 1.43/0.54    r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) | ~v1_funct_1(sK3)),
% 1.43/0.54    inference(subsumption_resolution,[],[f93,f31])).
% 1.43/0.54  fof(f93,plain,(
% 1.43/0.54    r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 1.43/0.54    inference(subsumption_resolution,[],[f89,f32])).
% 1.43/0.54  fof(f89,plain,(
% 1.43/0.54    r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 1.43/0.54    inference(resolution,[],[f68,f42])).
% 1.43/0.54  fof(f42,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X2,X3),X0) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f27])).
% 1.43/0.54  fof(f289,plain,(
% 1.43/0.54    ( ! [X2] : (r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),X2) | ~r1_tarski(sK0,X2) | ~r2_hidden(sK4(sK1,sK1),sK1)) )),
% 1.43/0.54    inference(resolution,[],[f264,f37])).
% 1.43/0.54  fof(f310,plain,(
% 1.43/0.54    ~r2_hidden(sK4(sK0,sK0),sK0)),
% 1.43/0.54    inference(resolution,[],[f307,f37])).
% 1.43/0.54  fof(f307,plain,(
% 1.43/0.54    ~r1_tarski(sK0,sK0)),
% 1.43/0.54    inference(subsumption_resolution,[],[f294,f34])).
% 1.43/0.54  fof(f294,plain,(
% 1.43/0.54    ~r1_tarski(sK0,sK0) | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 1.43/0.54    inference(resolution,[],[f290,f37])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (6249)------------------------------
% 1.43/0.54  % (6249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (6249)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (6249)Memory used [KB]: 1918
% 1.43/0.54  % (6249)Time elapsed: 0.082 s
% 1.43/0.54  % (6249)------------------------------
% 1.43/0.54  % (6249)------------------------------
% 1.43/0.54  % (6217)Success in time 0.19 s
%------------------------------------------------------------------------------

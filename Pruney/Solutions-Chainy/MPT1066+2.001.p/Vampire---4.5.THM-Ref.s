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
% DateTime   : Thu Dec  3 13:07:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 515 expanded)
%              Number of leaves         :   12 ( 219 expanded)
%              Depth                    :   28
%              Number of atoms          :  301 (3550 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2095)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f81])).

fof(f81,plain,(
    ~ r1_tarski(k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k3_tarski(sK3)) ),
    inference(superposition,[],[f56,f77])).

fof(f77,plain,(
    k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))) ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f73,plain,(
    m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k5_setfam_1(sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X1,k7_funct_2(sK0,X1,X2,k6_funct_2(sK0,X1,X2,X3))),k5_setfam_1(X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_setfam_1(X1,k7_funct_2(sK0,X1,X2,k6_funct_2(sK0,X1,X2,X3))),k5_setfam_1(X1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,X2,k6_funct_2(sK0,sK1,X2,X3))),k5_setfam_1(sK1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,X2,k6_funct_2(sK0,sK1,X2,X3))),k5_setfam_1(sK1,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,X3))),k5_setfam_1(sK1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,X3))),k5_setfam_1(sK1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
   => ( ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k5_setfam_1(sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                   => r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t183_funct_2)).

fof(f72,plain,
    ( m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,
    ( m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,
    ( m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f67,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | m1_subset_1(k7_funct_2(sK0,X0,X1,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v1_funct_2(X1,sK0,X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_funct_2(sK0,X0,X1,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_2(X1,sK0,X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f62,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(f62,plain,(
    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f61,plain,
    ( m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f60,f30])).

fof(f60,plain,
    ( m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f59,f31])).

fof(f59,plain,
    ( m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | m1_subset_1(k6_funct_2(X0,sK1,X1,sK3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f52,f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_funct_2(X0,sK1,X1,sK3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(f56,plain,(
    ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k3_tarski(sK3)) ),
    inference(superposition,[],[f34,f49])).

fof(f49,plain,(
    k5_setfam_1(sK1,sK3) = k3_tarski(sK3) ),
    inference(resolution,[],[f36,f33])).

fof(f34,plain,(
    ~ r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k5_setfam_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,(
    r1_tarski(k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k3_tarski(sK3)) ),
    inference(resolution,[],[f94,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f94,plain,(
    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(subsumption_resolution,[],[f93,f28])).

fof(f93,plain,
    ( m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f30])).

fof(f91,plain,
    ( m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f31])).

fof(f90,plain,
    ( m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f89,plain,
    ( m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f88,f33])).

fof(f88,plain,
    ( m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f80,f58])).

% (2114)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f58,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ m1_subset_1(k3_tarski(k7_funct_2(X2,X3,X4,k6_funct_2(X2,X3,X4,X1))),k1_zfmisc_1(X3))
      | m1_setfam_1(X1,k3_tarski(k7_funct_2(X2,X3,X4,k6_funct_2(X2,X3,X4,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X4,X2,X3)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4)
      | m1_setfam_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(X3,X4)
                      | ~ m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(X3,X4)
                      | ~ m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4)
                       => m1_setfam_1(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_funct_2)).

fof(f47,plain,(
    ! [X0] : m1_setfam_1(X0,k3_tarski(X0)) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    m1_subset_1(k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f76,f77])).

fof(f76,plain,(
    m1_subset_1(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (2101)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (2107)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (2099)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (2094)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (2091)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (2092)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (2099)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (2108)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (2093)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (2100)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (2095)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~r1_tarski(k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k3_tarski(sK3))),
% 0.21/0.51    inference(superposition,[],[f56,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))),
% 0.21/0.51    inference(resolution,[],[f73,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    (((~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k5_setfam_1(sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X1,k7_funct_2(sK0,X1,X2,k6_funct_2(sK0,X1,X2,X3))),k5_setfam_1(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X1,k7_funct_2(sK0,X1,X2,k6_funct_2(sK0,X1,X2,X3))),k5_setfam_1(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,X2,k6_funct_2(sK0,sK1,X2,X3))),k5_setfam_1(sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,X2,k6_funct_2(sK0,sK1,X2,X3))),k5_setfam_1(sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,X3))),k5_setfam_1(sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X3] : (~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,X3))),k5_setfam_1(sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) => (~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k5_setfam_1(sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) => r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) => r1_tarski(k5_setfam_1(X1,k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3))),k5_setfam_1(X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t183_funct_2)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1))) | v1_xboole_0(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~v1_funct_1(sK2) | v1_xboole_0(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    m1_subset_1(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f67,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | m1_subset_1(k7_funct_2(sK0,X0,X1,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v1_funct_2(X1,sK0,X0) | ~v1_funct_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f63,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k7_funct_2(sK0,X0,X1,k6_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(X1,sK0,X0) | ~v1_funct_1(X1) | v1_xboole_0(X0) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f62,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f61,f28])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f60,f30])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v1_funct_1(sK2) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f59,f31])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f53,f32])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k6_funct_2(X0,sK1,X1,sK3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f29])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k6_funct_2(X0,sK1,X1,sK3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(resolution,[],[f43,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k3_tarski(sK3))),
% 0.21/0.51    inference(superposition,[],[f34,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k5_setfam_1(sK1,sK3) = k3_tarski(sK3)),
% 0.21/0.51    inference(resolution,[],[f36,f33])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~r1_tarski(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k5_setfam_1(sK1,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    r1_tarski(k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k3_tarski(sK3))),
% 0.21/0.51    inference(resolution,[],[f94,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f28])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f29])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f30])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f90,f31])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f32])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f33])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    m1_setfam_1(sK3,k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f80,f58])).
% 0.21/0.51  % (2114)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X4,X2,X3,X1] : (~m1_subset_1(k3_tarski(k7_funct_2(X2,X3,X4,k6_funct_2(X2,X3,X4,X1))),k1_zfmisc_1(X3)) | m1_setfam_1(X1,k3_tarski(k7_funct_2(X2,X3,X4,k6_funct_2(X2,X3,X4,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X4,X2,X3) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f47,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4) | m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_setfam_1(X3,X4) | ~m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_setfam_1(X3,X4) | ~m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (m1_setfam_1(k7_funct_2(X0,X1,X2,k6_funct_2(X0,X1,X2,X3)),X4) => m1_setfam_1(X3,X4)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_funct_2)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (m1_setfam_1(X0,k3_tarski(X0))) )),
% 0.21/0.51    inference(resolution,[],[f42,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    m1_subset_1(k3_tarski(k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k1_zfmisc_1(sK1))),
% 0.21/0.51    inference(superposition,[],[f76,f77])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    m1_subset_1(k5_setfam_1(sK1,k7_funct_2(sK0,sK1,sK2,k6_funct_2(sK0,sK1,sK2,sK3))),k1_zfmisc_1(sK1))),
% 0.21/0.51    inference(resolution,[],[f73,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2099)------------------------------
% 0.21/0.51  % (2099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2099)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2099)Memory used [KB]: 10618
% 0.21/0.51  % (2099)Time elapsed: 0.097 s
% 0.21/0.51  % (2099)------------------------------
% 0.21/0.51  % (2099)------------------------------
% 0.21/0.51  % (2088)Success in time 0.152 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1038+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 295 expanded)
%              Number of leaves         :    9 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 (2953 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(subsumption_resolution,[],[f131,f108])).

fof(f108,plain,(
    v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f30,f104,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f104,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f103,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f103,plain,(
    ~ v1_partfun1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f24,f28,f26,f32,f33,f31,f25,f27,f30,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X4,X0)
      | r1_partfun1(X2,X3)
      | ~ r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X4) )
             => ( ( v1_partfun1(X4,X0)
                  & r1_partfun1(X3,X4)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_partfun1(sK1,sK2)
    & r1_partfun1(sK2,sK3)
    & r1_partfun1(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK3,sK0,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_partfun1(X1,X2)
                & r1_partfun1(X2,X3)
                & r1_partfun1(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(sK1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
              & v1_funct_2(X3,sK0,sK0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_partfun1(sK1,X2)
            & r1_partfun1(X2,X3)
            & r1_partfun1(sK1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
            & v1_funct_2(X3,sK0,sK0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_partfun1(sK1,sK2)
          & r1_partfun1(sK2,X3)
          & r1_partfun1(sK1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X3,sK0,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r1_partfun1(sK1,sK2)
        & r1_partfun1(sK2,X3)
        & r1_partfun1(sK1,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X3,sK0,sK0)
        & v1_funct_1(X3) )
   => ( ~ r1_partfun1(sK1,sK2)
      & r1_partfun1(sK2,sK3)
      & r1_partfun1(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK3,sK0,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                  & v1_funct_2(X3,X0,X0)
                  & v1_funct_1(X3) )
               => ( ( r1_partfun1(X2,X3)
                    & r1_partfun1(X1,X3) )
                 => r1_partfun1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
             => ( ( r1_partfun1(X2,X3)
                  & r1_partfun1(X1,X3) )
               => r1_partfun1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).

% (6311)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f91,f107,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | sQ4_eqProxy(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(equality_proxy_replacement,[],[f38,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f107,plain,(
    v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f27,f104,f36])).

fof(f91,plain,(
    ~ sQ4_eqProxy(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f80,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | sQ4_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f41])).

fof(f80,plain,(
    ~ sQ4_eqProxy(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f33,f31,f52,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X0,X1)
      | ~ r1_partfun1(X0,X2)
      | r1_partfun1(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f41])).

fof(f52,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f41])).

%------------------------------------------------------------------------------

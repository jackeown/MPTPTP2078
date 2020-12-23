%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 227 expanded)
%              Number of leaves         :   10 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 (1969 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f47,f92])).

fof(f92,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f76,f90])).

fof(f90,plain,
    ( r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f70,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f25,f39,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f39,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f17,f16,f15])).

fof(f15,plain,
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

fof(f16,plain,
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

fof(f17,plain,
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f70,plain,
    ( r1_partfun1(k1_xboole_0,sK3)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f26,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f48,f29])).

fof(f48,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f20,f39,f32])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,
    ( ~ r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f49,f29])).

fof(f49,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f22,f39,f32])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,
    ( ~ r1_partfun1(k1_xboole_0,sK2)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f28,f64])).

fof(f28,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f43,f45])).

fof(f45,plain,(
    ~ v1_partfun1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f19,f23,f21,f27,f28,f26,f20,f22,f25,f33])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_2
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f41,f37])).

fof(f35,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(global_subsumption,[],[f25,f23,f34])).

fof(f34,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:44:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (12440)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.48  % (12448)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.48  % (12437)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.48  % (12438)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.48  % (12440)Refutation not found, incomplete strategy% (12440)------------------------------
% 0.19/0.48  % (12440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12438)Refutation not found, incomplete strategy% (12438)------------------------------
% 0.19/0.49  % (12438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12432)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.49  % (12440)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (12440)Memory used [KB]: 10618
% 0.19/0.49  % (12440)Time elapsed: 0.089 s
% 0.19/0.49  % (12440)------------------------------
% 0.19/0.49  % (12440)------------------------------
% 0.19/0.49  % (12453)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.49  % (12451)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.49  % (12448)Refutation not found, incomplete strategy% (12448)------------------------------
% 0.19/0.49  % (12448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12450)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.49  % (12452)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.49  % (12452)Refutation not found, incomplete strategy% (12452)------------------------------
% 0.19/0.49  % (12452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12452)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (12452)Memory used [KB]: 6140
% 0.19/0.49  % (12452)Time elapsed: 0.098 s
% 0.19/0.49  % (12452)------------------------------
% 0.19/0.49  % (12452)------------------------------
% 0.19/0.49  % (12448)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (12448)Memory used [KB]: 1663
% 0.19/0.49  % (12448)Time elapsed: 0.104 s
% 0.19/0.49  % (12448)------------------------------
% 0.19/0.49  % (12448)------------------------------
% 0.19/0.50  % (12446)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.50  % (12436)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.50  % (12441)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.50  % (12446)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f44,f47,f92])).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    ~spl4_1),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f91])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    $false | ~spl4_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f76,f90])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    r1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl4_1),
% 0.19/0.50    inference(backward_demodulation,[],[f70,f82])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    k1_xboole_0 = sK3 | ~spl4_1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f50,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    v1_xboole_0(sK3) | ~spl4_1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f25,f39,f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    v1_xboole_0(sK0) | ~spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    spl4_1 <=> v1_xboole_0(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ((~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,sK3) & r1_partfun1(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK3,sK0,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f17,f16,f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (? [X3] : (~r1_partfun1(sK1,X2) & r1_partfun1(X2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : (~r1_partfun1(sK1,X2) & r1_partfun1(X2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) => (? [X3] : (~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ? [X3] : (~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) => (~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,sK3) & r1_partfun1(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK3,sK0,sK0) & v1_funct_1(sK3))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f8,plain,(
% 0.19/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.19/0.50    inference(flattening,[],[f7])).
% 0.19/0.50  fof(f7,plain,(
% 0.19/0.50    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_partfun1(X1,X2) & (r1_partfun1(X2,X3) & r1_partfun1(X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.19/0.50    inference(negated_conjecture,[],[f5])).
% 0.19/0.50  fof(f5,conjecture,(
% 0.19/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    r1_partfun1(k1_xboole_0,sK3) | ~spl4_1),
% 0.19/0.50    inference(backward_demodulation,[],[f26,f64])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    k1_xboole_0 = sK1 | ~spl4_1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f48,f29])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    v1_xboole_0(sK1) | ~spl4_1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f20,f39,f32])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    r1_partfun1(sK1,sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    ~r1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl4_1),
% 0.19/0.50    inference(backward_demodulation,[],[f71,f73])).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | ~spl4_1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f49,f29])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    v1_xboole_0(sK2) | ~spl4_1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f22,f39,f32])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ~r1_partfun1(k1_xboole_0,sK2) | ~spl4_1),
% 0.19/0.50    inference(backward_demodulation,[],[f28,f64])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ~r1_partfun1(sK1,sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ~spl4_2),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    $false | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f43,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ~v1_partfun1(sK3,sK0)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f19,f23,f21,f27,f28,f26,f20,f22,f25,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_partfun1(X4,X0) | r1_partfun1(X2,X3) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X2,X3) | ~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X2,X3) | (~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ((v1_partfun1(X4,X0) & r1_partfun1(X3,X4) & r1_partfun1(X2,X4)) => r1_partfun1(X2,X3)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    r1_partfun1(sK2,sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    v1_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    v1_funct_1(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    v1_funct_1(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    v1_partfun1(sK3,sK0) | ~spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    spl4_2 <=> v1_partfun1(sK3,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    spl4_1 | spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f35,f41,f37])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    v1_partfun1(sK3,sK0) | v1_xboole_0(sK0)),
% 0.19/0.50    inference(global_subsumption,[],[f25,f23,f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_xboole_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f31,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    v1_funct_2(sK3,sK0,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.50    inference(flattening,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (12446)------------------------------
% 0.19/0.50  % (12446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (12446)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (12446)Memory used [KB]: 10618
% 0.19/0.50  % (12446)Time elapsed: 0.101 s
% 0.19/0.50  % (12446)------------------------------
% 0.19/0.50  % (12446)------------------------------
% 0.19/0.50  % (12455)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.50  % (12445)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.50  % (12438)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (12431)Success in time 0.156 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:53 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 288 expanded)
%              Number of leaves         :    8 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 (2938 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f43])).

fof(f43,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f199,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(backward_demodulation,[],[f41,f159])).

fof(f159,plain,(
    sK2 = sK3 ),
    inference(unit_resulting_resolution,[],[f145,f156,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f156,plain,(
    v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f110,f127])).

fof(f127,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f108,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f108,plain,(
    ~ v1_partfun1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f34,f38,f36,f42,f43,f41,f35,f37,f40,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ v1_partfun1(X4,X0)
      | ~ r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f145,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f95,f127])).

fof(f95,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f37,f51])).

fof(f41,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (16427)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.18/0.46  % (16433)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.18/0.46  % (16433)Refutation not found, incomplete strategy% (16433)------------------------------
% 0.18/0.46  % (16433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (16427)Refutation not found, incomplete strategy% (16427)------------------------------
% 0.18/0.46  % (16427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (16433)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  % (16427)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  
% 0.18/0.46  % (16433)Memory used [KB]: 1663
% 0.18/0.46  % (16427)Memory used [KB]: 10490
% 0.18/0.46  % (16427)Time elapsed: 0.059 s
% 0.18/0.46  % (16433)Time elapsed: 0.064 s
% 0.18/0.46  % (16427)------------------------------
% 0.18/0.46  % (16427)------------------------------
% 0.18/0.46  % (16433)------------------------------
% 0.18/0.46  % (16433)------------------------------
% 0.18/0.48  % (16438)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.18/0.49  % (16434)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.18/0.49  % (16430)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.18/0.49  % (16434)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f206,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(subsumption_resolution,[],[f199,f43])).
% 0.18/0.49  fof(f43,plain,(
% 0.18/0.49    ~r1_partfun1(sK1,sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ((~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,sK3) & r1_partfun1(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK3,sK0,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25,f24])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (? [X3] : (~r1_partfun1(sK1,X2) & r1_partfun1(X2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ? [X2] : (? [X3] : (~r1_partfun1(sK1,X2) & r1_partfun1(X2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) => (? [X3] : (~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ? [X3] : (~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) => (~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,sK3) & r1_partfun1(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK3,sK0,sK0) & v1_funct_1(sK3))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.18/0.49    inference(flattening,[],[f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_partfun1(X1,X2) & (r1_partfun1(X2,X3) & r1_partfun1(X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.18/0.49    inference(ennf_transformation,[],[f12])).
% 0.18/0.49  fof(f12,negated_conjecture,(
% 0.18/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.18/0.49    inference(negated_conjecture,[],[f11])).
% 0.18/0.49  fof(f11,conjecture,(
% 0.18/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).
% 0.18/0.49  fof(f199,plain,(
% 0.18/0.49    r1_partfun1(sK1,sK2)),
% 0.18/0.49    inference(backward_demodulation,[],[f41,f159])).
% 0.18/0.49  fof(f159,plain,(
% 0.18/0.49    sK2 = sK3),
% 0.18/0.49    inference(unit_resulting_resolution,[],[f145,f156,f52])).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.18/0.49  fof(f156,plain,(
% 0.18/0.49    v1_xboole_0(sK3)),
% 0.18/0.49    inference(subsumption_resolution,[],[f110,f127])).
% 0.18/0.49  fof(f127,plain,(
% 0.18/0.49    v1_xboole_0(sK0)),
% 0.18/0.49    inference(unit_resulting_resolution,[],[f38,f39,f40,f108,f46])).
% 0.18/0.49  fof(f46,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.18/0.49    inference(flattening,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.18/0.49    inference(ennf_transformation,[],[f9])).
% 0.18/0.49  fof(f9,axiom,(
% 0.18/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.18/0.49  fof(f108,plain,(
% 0.18/0.49    ~v1_partfun1(sK3,sK0)),
% 0.18/0.49    inference(unit_resulting_resolution,[],[f34,f38,f36,f42,f43,f41,f35,f37,f40,f44])).
% 0.18/0.49  fof(f44,plain,(
% 0.18/0.49    ( ! [X4,X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X2,X3) | ~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.18/0.49    inference(flattening,[],[f15])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X2,X3) | (~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.18/0.49    inference(ennf_transformation,[],[f10])).
% 0.18/0.49  fof(f10,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ((v1_partfun1(X4,X0) & r1_partfun1(X3,X4) & r1_partfun1(X2,X4)) => r1_partfun1(X2,X3)))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).
% 0.18/0.49  fof(f37,plain,(
% 0.18/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f42,plain,(
% 0.18/0.49    r1_partfun1(sK2,sK3)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    v1_funct_1(sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f34,plain,(
% 0.18/0.49    v1_funct_1(sK1)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    v1_funct_2(sK3,sK0,sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f38,plain,(
% 0.18/0.49    v1_funct_1(sK3)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f110,plain,(
% 0.18/0.49    v1_xboole_0(sK3) | ~v1_xboole_0(sK0)),
% 0.18/0.49    inference(resolution,[],[f40,f51])).
% 0.18/0.49  fof(f51,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.18/0.49  fof(f145,plain,(
% 0.18/0.49    v1_xboole_0(sK2)),
% 0.18/0.49    inference(subsumption_resolution,[],[f95,f127])).
% 0.18/0.49  fof(f95,plain,(
% 0.18/0.49    v1_xboole_0(sK2) | ~v1_xboole_0(sK0)),
% 0.18/0.49    inference(resolution,[],[f37,f51])).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    r1_partfun1(sK1,sK3)),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (16434)------------------------------
% 0.18/0.49  % (16434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (16434)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (16434)Memory used [KB]: 1663
% 0.18/0.49  % (16434)Time elapsed: 0.081 s
% 0.18/0.49  % (16434)------------------------------
% 0.18/0.49  % (16434)------------------------------
% 0.18/0.49  % (16417)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.18/0.49  % (16416)Success in time 0.15 s
%------------------------------------------------------------------------------

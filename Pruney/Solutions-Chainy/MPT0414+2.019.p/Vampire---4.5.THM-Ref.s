%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (1745 expanded)
%              Number of leaves         :    2 ( 288 expanded)
%              Depth                    :   47
%              Number of atoms          :  238 (9467 expanded)
%              Number of equality atoms :   56 (1598 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(subsumption_resolution,[],[f169,f11])).

fof(f11,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f169,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f168,f102])).

fof(f102,plain,(
    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f101,f87])).

fof(f87,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f86,f10])).

fof(f10,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f85,f12])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f81,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2,X3),X0)
      | k4_subset_1(X0,X2,X3) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

% (5653)Refutation not found, incomplete strategy% (5653)------------------------------
% (5653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5653)Termination reason: Refutation not found, incomplete strategy

% (5653)Memory used [KB]: 10618
% (5653)Time elapsed: 0.063 s
% (5653)------------------------------
% (5653)------------------------------
% (5639)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (5642)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k4_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( r2_hidden(X4,X1)
                  <~> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k4_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( r2_hidden(X4,X1)
                  <~> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).

fof(f81,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),k1_zfmisc_1(sK0))
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) ),
    inference(resolution,[],[f55,f8])).

fof(f8,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f53,f10])).

fof(f53,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),sK1)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),X5)
      | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,X5) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X5] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),X5)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),sK1)
      | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,X5) ) ),
    inference(resolution,[],[f49,f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X1)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X0)
      | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f48,f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X1)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X0)
      | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X1)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X0)
      | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0 ) ),
    inference(resolution,[],[f41,f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(X0,X1,sK2,X2),k1_zfmisc_1(sK0))
      | r2_hidden(sK3(X0,X1,sK2,X2),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,sK2,X2),X2)
      | r2_hidden(sK3(X0,X1,sK2,X2),X1)
      | k4_subset_1(X0,sK2,X2) = X1 ) ),
    inference(resolution,[],[f8,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2,X3),X2)
      | r2_hidden(sK3(X0,X1,X2,X3),X3)
      | r2_hidden(sK3(X0,X1,X2,X3),X1)
      | k4_subset_1(X0,X2,X3) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f100,f10])).

fof(f100,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f99,f12])).

fof(f99,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f94,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3)
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X1)
      | k4_subset_1(X0,X2,X3) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f93,f10])).

fof(f93,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f92,f12])).

fof(f92,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f90,f16])).

fof(f90,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2)
    | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f87,f9])).

fof(f9,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f168,plain,(
    sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f167,f157])).

fof(f157,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) ),
    inference(subsumption_resolution,[],[f156,f11])).

fof(f156,plain,
    ( sK1 = sK2
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) ),
    inference(forward_demodulation,[],[f155,f102])).

fof(f155,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f154,f10])).

fof(f154,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f137,f16])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) ),
    inference(resolution,[],[f136,f9])).

fof(f136,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f135,f11])).

fof(f135,plain,
    ( sK1 = sK2
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) ),
    inference(forward_demodulation,[],[f134,f102])).

fof(f134,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f133,f120])).

fof(f120,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f119,f11])).

fof(f119,plain,
    ( sK1 = sK2
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) ),
    inference(forward_demodulation,[],[f118,f102])).

fof(f118,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f51,f10])).

fof(f51,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,X4),sK1)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,X4),X4)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,X4),sK2)
      | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,X4) ) ),
    inference(resolution,[],[f49,f10])).

fof(f133,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f132,f10])).

fof(f132,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f120,f14])).

fof(f167,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f166,f10])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)
    | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f157,f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (5646)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (5638)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (5653)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5645)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (5645)Refutation not found, incomplete strategy% (5645)------------------------------
% 0.21/0.47  % (5645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5645)Memory used [KB]: 6012
% 0.21/0.47  % (5645)Time elapsed: 0.003 s
% 0.21/0.47  % (5645)------------------------------
% 0.21/0.47  % (5645)------------------------------
% 0.21/0.47  % (5646)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    sK1 != sK2),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f4])).
% 0.21/0.48  fof(f4,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f2])).
% 0.21/0.48  fof(f2,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    sK1 = sK2),
% 0.21/0.48    inference(forward_demodulation,[],[f168,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.48    inference(resolution,[],[f81,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2,X3),X0) | k4_subset_1(X0,X2,X3) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  % (5653)Refutation not found, incomplete strategy% (5653)------------------------------
% 0.21/0.48  % (5653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5653)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (5653)Memory used [KB]: 10618
% 0.21/0.48  % (5653)Time elapsed: 0.063 s
% 0.21/0.48  % (5653)------------------------------
% 0.21/0.48  % (5653)------------------------------
% 0.21/0.49  % (5639)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (5642)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (! [X3] : (k4_subset_1(X0,X2,X3) = X1 | ? [X4] : ((r2_hidden(X4,X1) <~> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (! [X3] : ((k4_subset_1(X0,X2,X3) = X1 | ? [X4] : ((r2_hidden(X4,X1) <~> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) & m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),k1_zfmisc_1(sK0)) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)),
% 0.21/0.49    inference(resolution,[],[f55,f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | r2_hidden(X3,sK1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f53,f10])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),X5) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,X5)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X5] : (r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),X5) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,X5),sK1) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,X5)) )),
% 0.21/0.49    inference(resolution,[],[f49,f12])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X1) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X0) | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f48,f10])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X1) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X0) | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X1) | r2_hidden(sK3(k1_zfmisc_1(sK0),X0,sK2,X1),X0) | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = X0) )),
% 0.21/0.49    inference(resolution,[],[f41,f16])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(X0,X1,sK2,X2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(X0,X1,sK2,X2),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,sK2,X2),X2) | r2_hidden(sK3(X0,X1,sK2,X2),X1) | k4_subset_1(X0,sK2,X2) = X1) )),
% 0.21/0.49    inference(resolution,[],[f8,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2,X3),X2) | r2_hidden(sK3(X0,X1,X2,X3),X3) | r2_hidden(sK3(X0,X1,X2,X3),X1) | k4_subset_1(X0,X2,X3) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f10])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f12])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK1) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f94,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3) | ~r2_hidden(sK3(X0,X1,X2,X3),X1) | k4_subset_1(X0,X2,X3) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f10])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f12])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f90,f16])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2,sK2),sK2) | sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f87,f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f167,f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f156,f11])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    sK1 = sK2 | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f155,f102])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f154,f10])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f137,f16])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)),
% 0.21/0.49    inference(resolution,[],[f136,f9])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f11])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    sK1 = sK2 | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f134,f102])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f11])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK1 = sK2 | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f118,f102])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f51,f10])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,X4),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,X4),X4) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,X4),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,X4)) )),
% 0.21/0.49    inference(resolution,[],[f49,f10])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f10])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f120,f14])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f166,f10])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK2,sK2,sK2),sK2) | sK2 = k4_subset_1(k1_zfmisc_1(sK0),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f157,f14])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5646)------------------------------
% 0.21/0.49  % (5646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5646)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5646)Memory used [KB]: 1663
% 0.21/0.49  % (5646)Time elapsed: 0.010 s
% 0.21/0.49  % (5646)------------------------------
% 0.21/0.49  % (5646)------------------------------
% 0.21/0.49  % (5636)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (5632)Success in time 0.13 s
%------------------------------------------------------------------------------

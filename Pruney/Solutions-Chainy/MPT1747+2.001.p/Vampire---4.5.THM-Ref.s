%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  118 (1948 expanded)
%              Number of leaves         :   14 ( 727 expanded)
%              Depth                    :   27
%              Number of atoms          :  540 (25839 expanded)
%              Number of equality atoms :   69 (1790 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(subsumption_resolution,[],[f154,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f154,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f81,f147])).

fof(f147,plain,(
    k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f146,f142])).

fof(f142,plain,
    ( v3_pre_topc(sK5(sK1,sK4,sK3),sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f141,f117])).

fof(f117,plain,
    ( m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f116,f75])).

fof(f75,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(backward_demodulation,[],[f40,f69])).

fof(f69,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK1,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK4,sK1,sK2)
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))
    & u1_struct_0(sK2) = u1_struct_0(sK3)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      | ~ v5_pre_topc(X3,X0,X2)
                      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      | ~ v1_funct_1(X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X3,X0,X1)
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,sK1,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                  & v5_pre_topc(X3,sK1,X1)
                  & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                  | ~ v5_pre_topc(X3,sK1,X2)
                  | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                & v5_pre_topc(X3,sK1,X1)
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
            & u1_struct_0(X1) = u1_struct_0(X2)
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                | ~ v5_pre_topc(X3,sK1,X2)
                | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
              & v5_pre_topc(X3,sK1,sK2)
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK2))
          & u1_struct_0(X2) = u1_struct_0(sK2)
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
              | ~ v5_pre_topc(X3,sK1,X2)
              | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
            & v5_pre_topc(X3,sK1,sK2)
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK2))
        & u1_struct_0(X2) = u1_struct_0(sK2)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
            | ~ v5_pre_topc(X3,sK1,sK3)
            | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3))
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v5_pre_topc(X3,sK1,sK2)
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X3) )
      & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))
      & u1_struct_0(sK2) = u1_struct_0(sK3)
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

% (6245)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f27,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
          | ~ v5_pre_topc(X3,sK1,sK3)
          | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3))
          | ~ v1_funct_1(X3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v5_pre_topc(X3,sK1,sK2)
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK4,sK1,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v5_pre_topc(sK4,sK1,sK2)
      & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v5_pre_topc(X3,X0,X1)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v5_pre_topc(X3,X0,X1)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                  & u1_struct_0(X1) = u1_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v5_pre_topc(X3,X0,X1)
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X0,X2)
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tmap_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

% (6247)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f40,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f110,f64])).

fof(f64,plain,(
    ~ v5_pre_topc(sK4,sK1,sK3) ),
    inference(subsumption_resolution,[],[f63,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK4,sK1,sK3) ),
    inference(forward_demodulation,[],[f62,f40])).

fof(f62,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f43,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3) ),
    inference(backward_demodulation,[],[f60,f40])).

fof(f60,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f46,f42])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f110,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK4,sK1,sK3) ),
    inference(resolution,[],[f102,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | v5_pre_topc(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0)
            & v3_pre_topc(sK5(X0,X1,X2),X2)
            & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0)
        & v3_pre_topc(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
              & v3_pre_topc(X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              & v3_pre_topc(X3,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ! [X3] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> ! [X3] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f102,plain,
    ( sP0(sK1,sK4,sK3)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f101,f76])).

fof(f76,plain,(
    k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(forward_demodulation,[],[f70,f75])).

fof(f70,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,
    ( sP0(sK1,sK4,sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f100,f39])).

fof(f100,plain,
    ( sP0(sK1,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f99,f73])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f72,f69])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f45,f68])).

fof(f68,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f48,f65])).

fof(f65,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | sP0(sK1,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f96,f74])).

fof(f74,plain,(
    v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f71,f69])).

fof(f71,plain,(
    v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f43,f68])).

fof(f96,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | sP0(sK1,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(superposition,[],[f91,f75])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0))))
      | sP0(sK1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f90,f68])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0))
      | sP0(sK1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f87,f68])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0))
      | sP0(sK1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(resolution,[],[f86,f35])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | sP0(X1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | sP0(X0,X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f22])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f141,plain,
    ( ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_xboole_0 = k2_struct_0(sK2)
    | v3_pre_topc(sK5(sK1,sK4,sK3),sK2) ),
    inference(forward_demodulation,[],[f140,f69])).

fof(f140,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | v3_pre_topc(sK5(sK1,sK4,sK3),sK2)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f138,f37])).

fof(f138,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | v3_pre_topc(sK5(sK1,sK4,sK3),sK2)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f137,plain,
    ( r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK2))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(resolution,[],[f127,f41])).

fof(f41,plain,(
    r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(sK3),X0)
      | r2_hidden(sK5(sK1,sK4,sK3),X0)
      | k1_xboole_0 = k2_struct_0(sK2) ) ),
    inference(resolution,[],[f115,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f115,plain,
    ( r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f114,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | v5_pre_topc(sK4,sK1,sK3)
    | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f109,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | v5_pre_topc(sK4,sK1,sK3)
    | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f102,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X0,X2)
      | r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2)) ) ),
    inference(subsumption_resolution,[],[f84,f51])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2))
      | ~ m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X2)
      | v5_pre_topc(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f146,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(sK5(sK1,sK4,sK3),sK2) ),
    inference(subsumption_resolution,[],[f145,f113])).

fof(f113,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f112,f68])).

fof(f112,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f111,f75])).

fof(f111,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1) ),
    inference(subsumption_resolution,[],[f108,f64])).

fof(f108,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1)
    | v5_pre_topc(sK4,sK1,sK3) ),
    inference(resolution,[],[f102,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f145,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(sK5(sK1,sK4,sK3),sK2) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(sK5(sK1,sK4,sK3),sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(resolution,[],[f125,f117])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,X0),sK1)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2) ) ),
    inference(forward_demodulation,[],[f124,f68])).

fof(f124,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK4,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2) ) ),
    inference(forward_demodulation,[],[f123,f69])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0),sK1) ) ),
    inference(forward_demodulation,[],[f122,f69])).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f44,plain,(
    v5_pre_topc(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f118,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v5_pre_topc(sK4,sK1,sK2)
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0),sK1) ) ),
    inference(resolution,[],[f106,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v5_pre_topc(X1,X0,X2)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,
    ( sP0(sK1,sK4,sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f105,plain,
    ( sP0(sK1,sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f104,f73])).

fof(f104,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | sP0(sK1,sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f98,f74])).

fof(f98,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | sP0(sK1,sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(superposition,[],[f91,f69])).

fof(f81,plain,(
    ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f77,f67])).

fof(f77,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f58,f75])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:30:56 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.21/0.52  % (6249)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (6242)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (6249)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (6246)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6256)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (6243)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6258)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (6253)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (6264)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (6248)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.54  % (6261)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f157,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(subsumption_resolution,[],[f154,f47])).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    v1_xboole_0(k1_xboole_0)),
% 1.33/0.55    inference(cnf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    v1_xboole_0(k1_xboole_0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.33/0.55  fof(f154,plain,(
% 1.33/0.55    ~v1_xboole_0(k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f81,f147])).
% 1.33/0.55  fof(f147,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f146,f142])).
% 1.33/0.55  fof(f142,plain,(
% 1.33/0.55    v3_pre_topc(sK5(sK1,sK4,sK3),sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f141,f117])).
% 1.33/0.55  fof(f117,plain,(
% 1.33/0.55    m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(forward_demodulation,[],[f116,f75])).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    u1_struct_0(sK3) = k2_struct_0(sK2)),
% 1.33/0.55    inference(backward_demodulation,[],[f40,f69])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.33/0.55    inference(resolution,[],[f48,f66])).
% 1.33/0.55  fof(f66,plain,(
% 1.33/0.55    l1_struct_0(sK2)),
% 1.33/0.55    inference(resolution,[],[f49,f37])).
% 1.33/0.55  fof(f37,plain,(
% 1.33/0.55    l1_pre_topc(sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    ((((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK4,sK1,sK2) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK4)) & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) & u1_struct_0(sK2) = u1_struct_0(sK3) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f27,f26,f25,f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X3,sK1,X1) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X3,sK1,X1) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X3,sK1,sK2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK2)) & u1_struct_0(X2) = u1_struct_0(sK2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X3,sK1,sK2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK2)) & u1_struct_0(X2) = u1_struct_0(sK2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(X3,sK1,sK3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X3,sK1,sK2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) & u1_struct_0(sK2) = u1_struct_0(sK3) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  % (6245)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(X3,sK1,sK3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X3,sK1,sK2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK4,sK1,sK2) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK4))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f13,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/0.55    inference(flattening,[],[f12])).
% 1.33/0.55  fof(f12,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2))) & (l1_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.33/0.55    inference(ennf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,plain,(
% 1.33/0.55    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 1.33/0.55    inference(pure_predicate_removal,[],[f9])).
% 1.33/0.55  fof(f9,negated_conjecture,(
% 1.33/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 1.33/0.55    inference(negated_conjecture,[],[f8])).
% 1.33/0.55  fof(f8,conjecture,(
% 1.33/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tmap_1)).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f15])).
% 1.33/0.55  % (6247)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.55  fof(f15,plain,(
% 1.33/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f14])).
% 1.33/0.55  fof(f14,plain,(
% 1.33/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f116,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.33/0.55    inference(subsumption_resolution,[],[f110,f64])).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    ~v5_pre_topc(sK4,sK1,sK3)),
% 1.33/0.55    inference(subsumption_resolution,[],[f63,f45])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v5_pre_topc(sK4,sK1,sK3)),
% 1.33/0.55    inference(forward_demodulation,[],[f62,f40])).
% 1.33/0.55  fof(f62,plain,(
% 1.33/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3)),
% 1.33/0.55    inference(subsumption_resolution,[],[f61,f43])).
% 1.33/0.55  fof(f43,plain,(
% 1.33/0.55    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3)),
% 1.33/0.55    inference(backward_demodulation,[],[f60,f40])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))),
% 1.33/0.55    inference(subsumption_resolution,[],[f46,f42])).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    v1_funct_1(sK4)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f110,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) | v5_pre_topc(sK4,sK1,sK3)),
% 1.33/0.55    inference(resolution,[],[f102,f51])).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | v5_pre_topc(X1,X0,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f32])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 1.33/0.55    inference(rectify,[],[f29])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ! [X0,X2,X1] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~sP0(X0,X2,X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0,X2,X1] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~sP0(X0,X2,X1))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.33/0.55  fof(f102,plain,(
% 1.33/0.55    sP0(sK1,sK4,sK3) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(forward_demodulation,[],[f101,f76])).
% 1.33/0.55  fof(f76,plain,(
% 1.33/0.55    k2_struct_0(sK2) = k2_struct_0(sK3)),
% 1.33/0.55    inference(forward_demodulation,[],[f70,f75])).
% 1.33/0.55  fof(f70,plain,(
% 1.33/0.55    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.33/0.55    inference(resolution,[],[f48,f67])).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    l1_struct_0(sK3)),
% 1.33/0.55    inference(resolution,[],[f49,f39])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    l1_pre_topc(sK3)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f101,plain,(
% 1.33/0.55    sP0(sK1,sK4,sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 1.33/0.55    inference(subsumption_resolution,[],[f100,f39])).
% 1.33/0.55  fof(f100,plain,(
% 1.33/0.55    sP0(sK1,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 1.33/0.55    inference(subsumption_resolution,[],[f99,f73])).
% 1.33/0.55  fof(f73,plain,(
% 1.33/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 1.33/0.55    inference(backward_demodulation,[],[f72,f69])).
% 1.33/0.55  fof(f72,plain,(
% 1.33/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 1.33/0.55    inference(backward_demodulation,[],[f45,f68])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.33/0.55    inference(resolution,[],[f48,f65])).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    l1_struct_0(sK1)),
% 1.33/0.55    inference(resolution,[],[f49,f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    l1_pre_topc(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f99,plain,(
% 1.33/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | sP0(sK1,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 1.33/0.55    inference(subsumption_resolution,[],[f96,f74])).
% 1.33/0.55  fof(f74,plain,(
% 1.33/0.55    v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK2))),
% 1.33/0.55    inference(backward_demodulation,[],[f71,f69])).
% 1.33/0.55  fof(f71,plain,(
% 1.33/0.55    v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(sK2))),
% 1.33/0.55    inference(backward_demodulation,[],[f43,f68])).
% 1.33/0.55  fof(f96,plain,(
% 1.33/0.55    ~v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | sP0(sK1,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 1.33/0.55    inference(superposition,[],[f91,f75])).
% 1.33/0.55  fof(f91,plain,(
% 1.33/0.55    ( ! [X0] : (~v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) | sP0(sK1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f90,f68])).
% 1.33/0.55  fof(f90,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0)) | sP0(sK1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f87,f68])).
% 1.33/0.55  fof(f87,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0)) | sP0(sK1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 1.33/0.55    inference(resolution,[],[f86,f35])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | sP0(X1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 1.33/0.55    inference(resolution,[],[f54,f42])).
% 1.33/0.55  fof(f54,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | sP0(X0,X2,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f23])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (! [X2] : (sP0(X0,X2,X1) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(definition_folding,[],[f17,f22])).
% 1.33/0.55  fof(f17,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(flattening,[],[f16])).
% 1.33/0.55  fof(f16,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 1.33/0.55  fof(f141,plain,(
% 1.33/0.55    ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | v3_pre_topc(sK5(sK1,sK4,sK3),sK2)),
% 1.33/0.55    inference(forward_demodulation,[],[f140,f69])).
% 1.33/0.55  fof(f140,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | v3_pre_topc(sK5(sK1,sK4,sK3),sK2) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.33/0.55    inference(subsumption_resolution,[],[f138,f37])).
% 1.33/0.55  fof(f138,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | v3_pre_topc(sK5(sK1,sK4,sK3),sK2) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.33/0.55    inference(resolution,[],[f137,f57])).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(nnf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK2)) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(resolution,[],[f127,f41])).
% 1.33/0.55  fof(f41,plain,(
% 1.33/0.55    r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f127,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(u1_pre_topc(sK3),X0) | r2_hidden(sK5(sK1,sK4,sK3),X0) | k1_xboole_0 = k2_struct_0(sK2)) )),
% 1.33/0.55    inference(resolution,[],[f115,f59])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,plain,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.55  fof(f115,plain,(
% 1.33/0.55    r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3)) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f114,f64])).
% 1.33/0.55  fof(f114,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | v5_pre_topc(sK4,sK1,sK3) | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3))),
% 1.33/0.55    inference(subsumption_resolution,[],[f109,f39])).
% 1.33/0.55  fof(f109,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | ~l1_pre_topc(sK3) | v5_pre_topc(sK4,sK1,sK3) | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3))),
% 1.33/0.55    inference(resolution,[],[f102,f85])).
% 1.33/0.55  fof(f85,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~l1_pre_topc(X2) | v5_pre_topc(X1,X0,X2) | r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2))) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f84,f51])).
% 1.33/0.55  fof(f84,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2)) | ~m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | v5_pre_topc(X1,X0,X2) | ~sP0(X0,X1,X2)) )),
% 1.33/0.55    inference(resolution,[],[f56,f52])).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (v3_pre_topc(sK5(X0,X1,X2),X2) | v5_pre_topc(X1,X0,X2) | ~sP0(X0,X1,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f32])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f146,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(sK5(sK1,sK4,sK3),sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f145,f113])).
% 1.33/0.55  fof(f113,plain,(
% 1.33/0.55    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(forward_demodulation,[],[f112,f68])).
% 1.33/0.55  fof(f112,plain,(
% 1.33/0.55    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(forward_demodulation,[],[f111,f75])).
% 1.33/0.55  fof(f111,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f108,f64])).
% 1.33/0.55  fof(f108,plain,(
% 1.33/0.55    k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1) | v5_pre_topc(sK4,sK1,sK3)),
% 1.33/0.55    inference(resolution,[],[f102,f53])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0) | v5_pre_topc(X1,X0,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f32])).
% 1.33/0.55  fof(f145,plain,(
% 1.33/0.55    v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(sK5(sK1,sK4,sK3),sK2)),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f144])).
% 1.33/0.55  fof(f144,plain,(
% 1.33/0.55    v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,sK5(sK1,sK4,sK3)),sK1) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(sK5(sK1,sK4,sK3),sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(resolution,[],[f125,f117])).
% 1.33/0.55  fof(f125,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK4,X0),sK1) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f124,f68])).
% 1.33/0.55  fof(f124,plain,(
% 1.33/0.55    ( ! [X0] : (v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK4,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f123,f69])).
% 1.33/0.55  fof(f123,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0),sK1)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f122,f69])).
% 1.33/0.55  fof(f122,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0),sK1)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f118,f44])).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    v5_pre_topc(sK4,sK1,sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f118,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v5_pre_topc(sK4,sK1,sK2) | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0),sK1)) )),
% 1.33/0.55    inference(resolution,[],[f106,f50])).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~v5_pre_topc(X1,X0,X2) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f32])).
% 1.33/0.55  fof(f106,plain,(
% 1.33/0.55    sP0(sK1,sK4,sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f105,f37])).
% 1.33/0.55  fof(f105,plain,(
% 1.33/0.55    sP0(sK1,sK4,sK2) | ~l1_pre_topc(sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f104,f73])).
% 1.33/0.55  fof(f104,plain,(
% 1.33/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | sP0(sK1,sK4,sK2) | ~l1_pre_topc(sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(subsumption_resolution,[],[f98,f74])).
% 1.33/0.55  fof(f98,plain,(
% 1.33/0.55    ~v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | sP0(sK1,sK4,sK2) | ~l1_pre_topc(sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 1.33/0.55    inference(superposition,[],[f91,f69])).
% 1.33/0.55  fof(f81,plain,(
% 1.33/0.55    ~v1_xboole_0(k2_struct_0(sK2))),
% 1.33/0.55    inference(subsumption_resolution,[],[f80,f38])).
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ~v2_struct_0(sK3)),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f80,plain,(
% 1.33/0.55    ~v1_xboole_0(k2_struct_0(sK2)) | v2_struct_0(sK3)),
% 1.33/0.55    inference(subsumption_resolution,[],[f77,f67])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 1.33/0.55    inference(superposition,[],[f58,f75])).
% 1.33/0.55  fof(f58,plain,(
% 1.33/0.55    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/0.55    inference(flattening,[],[f19])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/0.55    inference(ennf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (6249)------------------------------
% 1.33/0.55  % (6249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (6249)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (6249)Memory used [KB]: 6396
% 1.33/0.55  % (6249)Time elapsed: 0.103 s
% 1.33/0.55  % (6249)------------------------------
% 1.33/0.55  % (6249)------------------------------
% 1.33/0.55  % (6241)Success in time 0.178 s
%------------------------------------------------------------------------------

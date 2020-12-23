%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  144 (1892 expanded)
%              Number of leaves         :   14 ( 731 expanded)
%              Depth                    :   47
%              Number of atoms          :  807 (26216 expanded)
%              Number of equality atoms :  107 (1730 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(resolution,[],[f373,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

% (10372)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f373,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f371,f69])).

fof(f69,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v5_pre_topc(sK3,sK0,sK2)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | ~ v1_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v5_pre_topc(sK3,sK0,sK1)
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24,f23,f22,f21])).

fof(f21,plain,
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
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,sK0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,sK0,X1)
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (10371)Refutation not found, incomplete strategy% (10371)------------------------------
% (10371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10371)Termination reason: Refutation not found, incomplete strategy

% (10371)Memory used [KB]: 10618
% (10371)Time elapsed: 0.082 s
% (10371)------------------------------
% (10371)------------------------------
fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                  | ~ v5_pre_topc(X3,sK0,X2)
                  | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v5_pre_topc(X3,sK0,X1)
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
            & u1_struct_0(X1) = u1_struct_0(X2)
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                | ~ v5_pre_topc(X3,sK0,X2)
                | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v5_pre_topc(X3,sK0,sK1)
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK1))
          & u1_struct_0(X2) = u1_struct_0(sK1)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
              | ~ v5_pre_topc(X3,sK0,X2)
              | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v5_pre_topc(X3,sK0,sK1)
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK1))
        & u1_struct_0(X2) = u1_struct_0(sK1)
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
            | ~ v5_pre_topc(X3,sK0,sK2)
            | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(X3,sK0,sK1)
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
      & u1_struct_0(sK1) = u1_struct_0(sK2)
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
          | ~ v5_pre_topc(X3,sK0,sK2)
          | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
          | ~ v1_funct_1(X3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(X3,sK0,sK1)
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        | ~ v5_pre_topc(sK3,sK0,sK2)
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v5_pre_topc(sK3,sK0,sK1)
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (10374)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
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
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tmap_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f371,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f253,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f253,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f83,f245])).

fof(f245,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f244,f77])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f75,f71])).

fof(f71,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f49,f68])).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f46,f70])).

fof(f70,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f244,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f243,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f243,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f232,f78])).

fof(f78,plain,(
    v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f74,f71])).

fof(f74,plain,(
    v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f44,f70])).

fof(f44,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f232,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f230,f81])).

fof(f81,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(forward_demodulation,[],[f79,f71])).

fof(f79,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(backward_demodulation,[],[f76,f71])).

fof(f76,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(forward_demodulation,[],[f73,f70])).

fof(f73,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(backward_demodulation,[],[f66,f70])).

fof(f66,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(forward_demodulation,[],[f65,f41])).

fof(f41,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(backward_demodulation,[],[f47,f41])).

fof(f47,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f230,plain,
    ( v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f229,f77])).

fof(f229,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f226,f152])).

fof(f152,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f147,f40])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(resolution,[],[f138,f78])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f135,f82])).

fof(f82,plain,(
    k2_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f72,f80])).

fof(f80,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f41,f71])).

fof(f72,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f49,f69])).

fof(f135,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(superposition,[],[f129,f80])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(sK0,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(forward_demodulation,[],[f128,f70])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(sK0,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(forward_demodulation,[],[f125,f70])).

fof(f125,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(sK0,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f119,f34])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK3,X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_subset_1(sK4(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v3_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v3_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
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
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f226,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f225,f40])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(resolution,[],[f223,f78])).

fof(f223,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f220,f207])).

fof(f207,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0)
    | ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(forward_demodulation,[],[f204,f82])).

fof(f204,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f187,f80])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f186,f70])).

fof(f186,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0) ) ),
    inference(forward_demodulation,[],[f185,f70])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0) ) ),
    inference(forward_demodulation,[],[f182,f70])).

fof(f182,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0) ) ),
    inference(resolution,[],[f134,f34])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK3,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK4(X0,X1,sK3)),X0) ) ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f220,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(resolution,[],[f218,f180])).

fof(f180,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK3),sK1)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK3),sK1)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2)
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f177,f156])).

fof(f156,plain,
    ( r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f154,f77])).

fof(f154,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2)
    | r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1)) ),
    inference(resolution,[],[f152,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f177,plain,
    ( ~ r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1))
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK1)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(resolution,[],[f175,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f175,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | v5_pre_topc(sK3,sK0,sK2)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK1)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f167,f37])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f165,f71])).

fof(f165,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f164,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f164,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(resolution,[],[f163,f42])).

fof(f42,plain,(
    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(sK2),X0)
      | r2_hidden(sK4(sK0,sK2,sK3),X0)
      | k1_xboole_0 = k2_struct_0(sK1)
      | v5_pre_topc(sK3,sK0,sK2) ) ),
    inference(resolution,[],[f161,f64])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X0))
      | v5_pre_topc(sK3,sK0,sK2)
      | r2_hidden(sK4(sK0,sK2,sK3),X0)
      | k1_xboole_0 = k2_struct_0(sK1) ) ),
    inference(resolution,[],[f159,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f159,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(resolution,[],[f156,f121])).

fof(f121,plain,
    ( ~ r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1))
    | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(resolution,[],[f120,f64])).

fof(f120,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | v5_pre_topc(sK3,sK0,sK2)
    | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f118,f40])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2)
    | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f117,f80])).

fof(f117,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2)
    | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f115,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f115,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK3),sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK3,sK0,sK2) ),
    inference(resolution,[],[f114,f77])).

fof(f114,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK2) ),
    inference(resolution,[],[f113,f40])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK2) ),
    inference(resolution,[],[f101,f78])).

fof(f101,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK2) ),
    inference(forward_demodulation,[],[f98,f82])).

fof(f98,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ l1_pre_topc(sK2)
    | v3_pre_topc(sK4(sK0,sK2,sK3),sK2) ),
    inference(superposition,[],[f93,f80])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(sK4(sK0,X0,sK3),X0) ) ),
    inference(forward_demodulation,[],[f92,f70])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k1_xboole_0 = k2_struct_0(X0)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(sK4(sK0,X0,sK3),X0) ) ),
    inference(forward_demodulation,[],[f89,f70])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK3,sK0,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(sK4(sK0,X0,sK3),X0) ) ),
    inference(resolution,[],[f88,f34])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK3,X0,X1)
      | ~ l1_pre_topc(X1)
      | v3_pre_topc(sK4(X0,X1,sK3),X1) ) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v3_pre_topc(sK4(X0,X1,X2),X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | k1_xboole_0 = k2_struct_0(sK1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ) ),
    inference(resolution,[],[f217,f34])).

fof(f217,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ) ),
    inference(resolution,[],[f216,f37])).

fof(f216,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f203,f78])).

fof(f203,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f202,f70])).

fof(f202,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0)
      | ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f201,f71])).

fof(f201,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f200,f70])).

fof(f200,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f199,f71])).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f198,f70])).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f197,f71])).

fof(f197,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f196,f71])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | k1_xboole_0 = k2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f162,f45])).

fof(f45,plain,(
    v5_pre_topc(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK3,X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK3,X0),X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f61,f80])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:01:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (10377)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.48  % (10370)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (10385)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.50  % (10386)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.50  % (10371)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (10377)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(resolution,[],[f373,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  % (10372)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f371,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    l1_struct_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f50,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    l1_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ((((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK3,sK0,sK1) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24,f23,f22,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X3,sK0,X1) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (10371)Refutation not found, incomplete strategy% (10371)------------------------------
% 0.22/0.50  % (10371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (10371)Memory used [KB]: 10618
% 0.22/0.50  % (10371)Time elapsed: 0.082 s
% 0.22/0.50  % (10371)------------------------------
% 0.22/0.50  % (10371)------------------------------
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X3,sK0,X1) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X3,sK0,sK1) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK1)) & u1_struct_0(X2) = u1_struct_0(sK1) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X3,sK0,sK1) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK1)) & u1_struct_0(X2) = u1_struct_0(sK1) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(X3,sK0,sK2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X3,sK0,sK1) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(X3,sK0,sK2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X3,sK0,sK1) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK3,sK0,sK1) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (10374)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tmap_1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f371,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f253,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~v2_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    v2_struct_0(sK2) | ~l1_struct_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f83,f245])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f244,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    inference(backward_demodulation,[],[f75,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f49,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    l1_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f50,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    l1_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(backward_demodulation,[],[f46,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f49,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f50,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f243,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f232,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.50    inference(backward_demodulation,[],[f74,f71])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(backward_demodulation,[],[f44,f70])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f230,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(forward_demodulation,[],[f79,f71])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(backward_demodulation,[],[f76,f71])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(forward_demodulation,[],[f73,f70])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(backward_demodulation,[],[f66,f70])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(forward_demodulation,[],[f65,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(backward_demodulation,[],[f47,f41])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f229,f77])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f227])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    inference(resolution,[],[f226,f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    inference(resolution,[],[f147,f40])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.22/0.50    inference(resolution,[],[f138,f78])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.22/0.50    inference(forward_demodulation,[],[f135,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f72,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    u1_struct_0(sK2) = k2_struct_0(sK1)),
% 0.22/0.50    inference(backward_demodulation,[],[f41,f71])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f49,f69])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK2) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.22/0.50    inference(superposition,[],[f129,f80])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK4(sK0,X0,sK3),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f128,f70])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK4(sK0,X0,sK3),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f125,f70])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_struct_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK4(sK0,X0,sK3),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(resolution,[],[f119,f34])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK3,X0,X1) | ~l1_pre_topc(X1) | m1_subset_1(sK4(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.22/0.50    inference(resolution,[],[f53,f43])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    inference(resolution,[],[f225,f40])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.22/0.50    inference(resolution,[],[f223,f78])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f221])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(resolution,[],[f220,f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0) | ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f204,f82])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK2) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(superposition,[],[f187,f80])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0)) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f186,f70])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f185,f70])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f182,f70])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_struct_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK3,sK4(sK0,X0,sK3)),sK0)) )),
% 0.22/0.50    inference(resolution,[],[f134,f34])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK3,X0,X1) | ~l1_pre_topc(X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK4(X0,X1,sK3)),X0)) )),
% 0.22/0.50    inference(resolution,[],[f57,f43])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,sK4(sK0,sK2,sK3)),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f218,f180])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    v3_pre_topc(sK4(sK0,sK2,sK3),sK1) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    v3_pre_topc(sK4(sK0,sK2,sK3),sK1) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f177,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1)) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f154,f77])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2) | r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1))),
% 0.22/0.50    inference(resolution,[],[f152,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ~r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1)) | v3_pre_topc(sK4(sK0,sK2,sK3),sK1) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f175,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(sK3,sK0,sK2) | v3_pre_topc(sK4(sK0,sK2,sK3),sK1) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f167,f37])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2) | v3_pre_topc(sK4(sK0,sK2,sK3),sK1) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.22/0.50    inference(forward_demodulation,[],[f165,f71])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2) | v3_pre_topc(sK4(sK0,sK2,sK3),sK1) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.50    inference(resolution,[],[f164,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f163,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(u1_pre_topc(sK2),X0) | r2_hidden(sK4(sK0,sK2,sK3),X0) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)) )),
% 0.22/0.50    inference(resolution,[],[f161,f64])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X0)) | v5_pre_topc(sK3,sK0,sK2) | r2_hidden(sK4(sK0,sK2,sK3),X0) | k1_xboole_0 = k2_struct_0(sK1)) )),
% 0.22/0.50    inference(resolution,[],[f159,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f156,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ~r1_tarski(sK4(sK0,sK2,sK3),k2_struct_0(sK1)) | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f120,f64])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(sK3,sK0,sK2) | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2)) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f118,f40])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2) | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2)) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.22/0.50    inference(forward_demodulation,[],[f117,f80])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2) | r2_hidden(sK4(sK0,sK2,sK3),u1_pre_topc(sK2)) | ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(resolution,[],[f115,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    v3_pre_topc(sK4(sK0,sK2,sK3),sK2) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f114,f77])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(sK4(sK0,sK2,sK3),sK2)),
% 0.22/0.50    inference(resolution,[],[f113,f40])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(sK4(sK0,sK2,sK3),sK2)),
% 0.22/0.50    inference(resolution,[],[f101,f78])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2) | v3_pre_topc(sK4(sK0,sK2,sK3),sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f98,f82])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK2) | v5_pre_topc(sK3,sK0,sK2) | ~l1_pre_topc(sK2) | v3_pre_topc(sK4(sK0,sK2,sK3),sK2)),
% 0.22/0.50    inference(superposition,[],[f93,f80])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | v3_pre_topc(sK4(sK0,X0,sK3),X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f92,f70])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | v3_pre_topc(sK4(sK0,X0,sK3),X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f89,f70])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_struct_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK3,sK0,X0) | ~l1_pre_topc(X0) | v3_pre_topc(sK4(sK0,X0,sK3),X0)) )),
% 0.22/0.50    inference(resolution,[],[f88,f34])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK3,X0,X1) | ~l1_pre_topc(X1) | v3_pre_topc(sK4(X0,X1,sK3),X1)) )),
% 0.22/0.50    inference(resolution,[],[f55,f43])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | v3_pre_topc(sK4(X0,X1,X2),X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))) )),
% 0.22/0.50    inference(resolution,[],[f217,f34])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))) )),
% 0.22/0.50    inference(resolution,[],[f216,f37])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f203,f78])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f202,f70])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK3,X0),sK0) | ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f201,f71])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f200,f70])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f199,f71])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f198,f70])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f197,f71])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f196,f71])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f162,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    v5_pre_topc(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v5_pre_topc(sK3,X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK3,X0),X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(resolution,[],[f51,f43])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.22/0.50    inference(superposition,[],[f61,f80])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (10377)------------------------------
% 0.22/0.50  % (10377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10377)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (10377)Memory used [KB]: 1918
% 0.22/0.50  % (10377)Time elapsed: 0.068 s
% 0.22/0.50  % (10377)------------------------------
% 0.22/0.50  % (10377)------------------------------
% 0.22/0.51  % (10367)Success in time 0.147 s
%------------------------------------------------------------------------------

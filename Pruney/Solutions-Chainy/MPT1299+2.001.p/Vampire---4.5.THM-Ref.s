%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 760 expanded)
%              Number of leaves         :    8 ( 204 expanded)
%              Depth                    :   30
%              Number of atoms          :  285 (4408 expanded)
%              Number of equality atoms :   36 ( 249 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(global_subsumption,[],[f27,f388,f390])).

fof(f390,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f389,f388])).

fof(f389,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f381,f42])).

fof(f42,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v1_tops_2(sK1,sK0) )
    & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | ~ v1_tops_2(X1,sK0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | ~ v1_tops_2(X1,sK0) )
        & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | v1_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v1_tops_2(sK1,sK0) )
      & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | v1_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

% (15138)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

fof(f381,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f40,f177])).

fof(f177,plain,(
    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f176,f42])).

fof(f176,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f175,f25])).

fof(f175,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f173,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f173,plain,
    ( ~ m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f172,f96])).

fof(f96,plain,
    ( ~ m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f95,f25])).

fof(f95,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f70,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

% (15132)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f70,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) ),
    inference(resolution,[],[f43,f42])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),sK1)
      | sK1 = k7_setfam_1(u1_struct_0(sK0),X0)
      | r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),X0,sK1)),X0) ) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f172,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f169,f25])).

fof(f169,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f165,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f165,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f164,f42])).

fof(f164,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f162,f44])).

fof(f44,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(u1_struct_0(sK0),X1,sK1),sK1)
      | ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),X1,sK1)),X1)
      | k7_setfam_1(u1_struct_0(sK0),X1) = sK1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f162,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f161,f42])).

fof(f161,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f160,f25])).

fof(f160,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f96,f35])).

fof(f40,plain,(
    ! [X0] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v2_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f388,plain,(
    v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f387,f26])).

fof(f26,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f387,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f380,f42])).

fof(f380,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f41,f177])).

fof(f41,plain,(
    ! [X1] :
      ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v2_tops_2(X1,sK0) ) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (15141)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (15134)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (15133)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (15142)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (15141)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f27,f388,f390])).
% 0.21/0.49  fof(f390,plain,(
% 0.21/0.49    v1_tops_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f389,f388])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    v1_tops_2(sK1,sK0) | ~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f381,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f25,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tops_2(sK1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | ~v1_tops_2(X1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | ~v1_tops_2(X1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tops_2(sK1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (15138)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    v1_tops_2(sK1,sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(superposition,[],[f40,f177])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f42])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(subsumption_resolution,[],[f175,f25])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(resolution,[],[f173,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(rectify,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f172,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f25])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | ~m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | ~m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(resolution,[],[f70,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  % (15132)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1)),
% 0.21/0.49    inference(resolution,[],[f43,f42])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),sK1) | sK1 = k7_setfam_1(u1_struct_0(sK0),X0) | r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),X0,sK1)),X0)) )),
% 0.21/0.49    inference(resolution,[],[f25,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | ~m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f169,f25])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | ~m1_subset_1(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(resolution,[],[f165,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f164,f42])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(resolution,[],[f162,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK2(u1_struct_0(sK0),X1,sK1),sK1) | ~r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0),X1,sK1)),X1) | k7_setfam_1(u1_struct_0(sK0),X1) = sK1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.21/0.49    inference(resolution,[],[f25,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f161,f42])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f25])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    r2_hidden(sK2(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1),sK1),sK1) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    inference(resolution,[],[f96,f35])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_2(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f24,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f388,plain,(
% 0.21/0.49    v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f387,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    ~v1_tops_2(sK1,sK0) | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f380,f42])).
% 0.21/0.49  fof(f380,plain,(
% 0.21/0.49    ~v1_tops_2(sK1,sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    inference(superposition,[],[f41,f177])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X1,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f24,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tops_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15141)------------------------------
% 0.21/0.49  % (15141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15141)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15141)Memory used [KB]: 6396
% 0.21/0.49  % (15141)Time elapsed: 0.025 s
% 0.21/0.49  % (15141)------------------------------
% 0.21/0.49  % (15141)------------------------------
% 0.21/0.49  % (15139)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (15139)Refutation not found, incomplete strategy% (15139)------------------------------
% 0.21/0.49  % (15139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15139)Memory used [KB]: 1535
% 0.21/0.49  % (15139)Time elapsed: 0.067 s
% 0.21/0.49  % (15139)------------------------------
% 0.21/0.49  % (15139)------------------------------
% 0.21/0.49  % (15125)Success in time 0.136 s
%------------------------------------------------------------------------------

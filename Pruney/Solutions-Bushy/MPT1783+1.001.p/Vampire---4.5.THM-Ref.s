%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 336 expanded)
%              Number of leaves         :    9 ( 106 expanded)
%              Depth                    :   24
%              Number of atoms          :  379 (2808 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f244,f141])).

fof(f141,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f140,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f22,f21])).

% (1217)Termination reason: Refutation not found, incomplete strategy
fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v5_pre_topc(k4_tmap_1(X0,X1),X1,X0)
              | ~ v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(k4_tmap_1(X0,X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k4_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            | ~ v5_pre_topc(k4_tmap_1(sK0,X1),X1,sK0)
            | ~ v1_funct_2(k4_tmap_1(sK0,X1),u1_struct_0(X1),u1_struct_0(sK0))
            | ~ v1_funct_1(k4_tmap_1(sK0,X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k4_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
          | ~ v5_pre_topc(k4_tmap_1(sK0,X1),X1,sK0)
          | ~ v1_funct_2(k4_tmap_1(sK0,X1),u1_struct_0(X1),u1_struct_0(sK0))
          | ~ v1_funct_1(k4_tmap_1(sK0,X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (1217)Memory used [KB]: 10618
fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k4_tmap_1(X0,X1),X1,X0)
            | ~ v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k4_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

% (1217)Time elapsed: 0.095 s
fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k4_tmap_1(X0,X1),X1,X0)
            | ~ v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k4_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (1217)------------------------------
% (1217)------------------------------
fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(k4_tmap_1(X0,X1),X1,X0)
              & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(k4_tmap_1(X0,X1),X1,X0)
            & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_tmap_1)).

fof(f140,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f25])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f139,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f130,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f244,plain,(
    ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f243,f144])).

fof(f144,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f143,f24])).

fof(f143,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f25])).

fof(f142,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f131,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f243,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f239,f147])).

fof(f147,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f146,f24])).

fof(f146,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f145,f25])).

fof(f145,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f26])).

fof(f132,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f239,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f235,f29])).

fof(f29,plain,
    ( ~ v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f235,plain,(
    v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0) ),
    inference(subsumption_resolution,[],[f234,f24])).

fof(f234,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f25])).

fof(f233,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f232,f26])).

fof(f232,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f231,f61])).

fof(f61,plain,(
    v1_funct_1(k3_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f60,f25])).

fof(f60,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f44,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v5_pre_topc(k3_struct_0(X0),X0,X0)
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v5_pre_topc(k3_struct_0(X0),X0,X0)
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k3_struct_0(X0),X0,X0)
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tmap_1)).

fof(f231,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f63])).

fof(f63,plain,(
    v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f62,f25])).

fof(f62,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f45,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f24,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f230,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f65])).

fof(f65,plain,(
    v5_pre_topc(k3_struct_0(sK0),sK0,sK0) ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f64,plain,
    ( v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f46,f26])).

fof(f46,plain,
    ( v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f24,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v5_pre_topc(k3_struct_0(X0),X0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f229,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f162])).

fof(f162,plain,(
    m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f99,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_struct_0)).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f228,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f227,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f227,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f28])).

fof(f224,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k3_struct_0(sK0),sK0,sK0)
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f43,f138])).

% (1237)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f138,plain,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f137,f24])).

fof(f137,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f25])).

fof(f136,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f129,f26])).

fof(f129,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tmap_1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

%------------------------------------------------------------------------------

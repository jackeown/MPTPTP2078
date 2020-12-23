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
% DateTime   : Thu Dec  3 13:20:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  159 (1664 expanded)
%              Number of leaves         :   20 ( 498 expanded)
%              Depth                    :   25
%              Number of atoms          :  543 (7651 expanded)
%              Number of equality atoms :   27 (1197 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(subsumption_resolution,[],[f385,f330])).

fof(f330,plain,(
    v3_pre_topc(sK2(sK1),sK0) ),
    inference(resolution,[],[f308,f291])).

fof(f291,plain,(
    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f289,f125])).

fof(f125,plain,(
    v3_pre_topc(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f124,f54])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v3_tdlat_3(sK1)
    & v3_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tdlat_3(X1)
            & v3_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ~ v3_tdlat_3(X1)
        & v3_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v3_tdlat_3(sK1)
      & v3_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

fof(f124,plain,
    ( v3_pre_topc(sK2(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f123,f57])).

fof(f57,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f123,plain,
    ( v3_pre_topc(sK2(sK1),sK1)
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f119,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(sK1))
      | v3_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f117,f100])).

fof(f100,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X1,u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f96,f54])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f82,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f117,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f289,plain,
    ( ~ v3_pre_topc(sK2(sK1),sK1)
    | r2_hidden(sK2(sK1),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f224,f171])).

fof(f171,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f170,f54])).

fof(f170,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f168,f57])).

fof(f168,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f164,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f164,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f121,f151])).

fof(f151,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f139,f88])).

fof(f88,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f58,f54])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f139,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f110,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f78,f53])).

% (15143)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f110,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f109,f55])).

fof(f55,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    inference(subsumption_resolution,[],[f107,f92])).

fof(f92,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f67,f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f69,f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f224,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK1)
      | r2_hidden(X1,u1_pre_topc(sK1)) ) ),
    inference(superposition,[],[f115,f218])).

fof(f218,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f217,f87])).

fof(f87,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f58,f53])).

fof(f217,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK0) ),
    inference(subsumption_resolution,[],[f215,f151])).

fof(f215,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f210,f132])).

fof(f132,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f108,f104])).

fof(f104,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f103,f55])).

fof(f103,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f78,f54])).

fof(f108,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f106,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f67,f53])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f65,f53])).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(X0) = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f202,f53])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f200,f67])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f68,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f115,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | r2_hidden(X1,u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f71,f54])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f308,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f307,f87])).

fof(f307,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK0,sK0) ) ),
    inference(resolution,[],[f304,f132])).

fof(f304,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,sK1)
      | v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f207,f220])).

fof(f220,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f193,f204])).

fof(f204,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f203,f54])).

fof(f203,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f180,f60])).

fof(f180,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f130,f151])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f70,f53])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X0,sK1)
      | v1_tops_2(u1_pre_topc(sK1),X0) ) ),
    inference(resolution,[],[f135,f90])).

fof(f90,plain,(
    v1_tops_2(u1_pre_topc(sK1),sK1) ),
    inference(resolution,[],[f59,f54])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_2(u1_pre_topc(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

fof(f135,plain,(
    ! [X2,X3] :
      ( ~ v1_tops_2(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ m1_pre_topc(X3,sK1)
      | v1_tops_2(X2,X3) ) ),
    inference(resolution,[],[f86,f54])).

fof(f86,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | v1_tops_2(X3,X2) ) ),
    inference(subsumption_resolution,[],[f83,f70])).

fof(f83,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f207,plain,(
    ! [X0] :
      ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
      | ~ r2_hidden(X0,u1_pre_topc(sK1))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f204,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f147,f82])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f73,f53])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v3_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f385,plain,(
    ~ v3_pre_topc(sK2(sK1),sK0) ),
    inference(resolution,[],[f379,f174])).

fof(f174,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK2(sK1),sK0) ),
    inference(resolution,[],[f171,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f71,f53])).

fof(f379,plain,(
    ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f378,f53])).

fof(f378,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f377,f56])).

fof(f56,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f377,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f376,f171])).

fof(f376,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f369,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f369,plain,(
    ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f362,f312])).

fof(f312,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f311,f53])).

fof(f311,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f309,f283])).

fof(f283,plain,(
    v1_tops_2(u1_pre_topc(sK0),sK1) ),
    inference(subsumption_resolution,[],[f282,f53])).

fof(f282,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f246,f60])).

fof(f246,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(u1_pre_topc(sK0),sK1) ),
    inference(subsumption_resolution,[],[f239,f151])).

fof(f239,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK1,sK0)
    | v1_tops_2(u1_pre_topc(sK0),sK1) ),
    inference(superposition,[],[f190,f218])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X0,sK0)
      | v1_tops_2(u1_pre_topc(sK0),X0) ) ),
    inference(resolution,[],[f134,f89])).

fof(f89,plain,(
    v1_tops_2(u1_pre_topc(sK0),sK0) ),
    inference(resolution,[],[f59,f53])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,sK0)
      | v1_tops_2(X0,X1) ) ),
    inference(resolution,[],[f86,f53])).

fof(f309,plain,(
    ! [X0] :
      ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f226,f60])).

fof(f226,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X3,sK1)
      | ~ r2_hidden(X4,X3)
      | v3_pre_topc(X4,sK1) ) ),
    inference(superposition,[],[f150,f218])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | ~ v1_tops_2(X3,sK1)
      | ~ r2_hidden(X2,X3)
      | v3_pre_topc(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f148,f82])).

fof(f148,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_tops_2(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | v3_pre_topc(X2,sK1) ) ),
    inference(resolution,[],[f73,f54])).

fof(f362,plain,
    ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f287,f242])).

% (15136)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f242,plain,(
    ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f241,f54])).

fof(f241,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f233,f57])).

fof(f233,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f64,f218])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f287,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_pre_topc(sK1))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r2_hidden(X1,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f224,f99])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f96,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:41:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.45  % (15132)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.46  % (15140)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.47  % (15127)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.48  % (15140)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (15148)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f386,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f385,f330])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    v3_pre_topc(sK2(sK1),sK0)),
% 0.20/0.48    inference(resolution,[],[f308,f291])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    r2_hidden(sK2(sK1),u1_pre_topc(sK1))),
% 0.20/0.48    inference(subsumption_resolution,[],[f289,f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    v3_pre_topc(sK2(sK1),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f124,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    l1_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    (~v3_tdlat_3(sK1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f16])).
% 0.20/0.49  fof(f16,conjecture,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    v3_pre_topc(sK2(sK1),sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f123,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ~v3_tdlat_3(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    v3_pre_topc(sK2(sK1),sK1) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f119,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK2(X0),u1_pre_topc(X0)) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK1)) | v3_pre_topc(X1,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f117,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X1,u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f96,f54])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~r2_hidden(X0,u1_pre_topc(X1)) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f82,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f72,f54])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    ~v3_pre_topc(sK2(sK1),sK1) | r2_hidden(sK2(sK1),u1_pre_topc(sK1))),
% 0.20/0.49    inference(resolution,[],[f224,f171])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f170,f54])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f57])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f164,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.49    inference(resolution,[],[f121,f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f139,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK1)),
% 0.20/0.49    inference(resolution,[],[f58,f54])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK1) | m1_pre_topc(X1,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f110,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f78,f53])).
% 0.20/0.49  % (15143)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f109,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK1) | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f107,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK1) | l1_pre_topc(X1)) )),
% 0.20/0.49    inference(resolution,[],[f67,f54])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK1) | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1)) )),
% 0.20/0.49    inference(resolution,[],[f65,f54])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.49    inference(resolution,[],[f69,f53])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK1) | r2_hidden(X1,u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(superposition,[],[f115,f218])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f217,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0)),
% 0.20/0.49    inference(resolution,[],[f58,f53])).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    u1_struct_0(sK0) = u1_struct_0(sK1) | ~m1_pre_topc(sK0,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f215,f151])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0) | u1_struct_0(sK0) = u1_struct_0(sK1) | ~m1_pre_topc(sK0,sK0)),
% 0.20/0.49    inference(resolution,[],[f210,f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f108,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f103,f55])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f78,f54])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f106,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f67,f53])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f65,f53])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = u1_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f202,f53])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,X1) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f200,f67])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.49    inference(resolution,[],[f95,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X1) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f68,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | r2_hidden(X1,u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f71,f54])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f46])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK1)) | v3_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f307,f87])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~r2_hidden(X0,u1_pre_topc(sK1)) | ~m1_pre_topc(sK0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f304,f132])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK0,sK1) | v3_pre_topc(X0,sK0) | ~r2_hidden(X0,u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f207,f220])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    v1_tops_2(u1_pre_topc(sK1),sK0) | ~m1_pre_topc(sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f193,f204])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    inference(subsumption_resolution,[],[f203,f54])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f180,f60])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.49    inference(resolution,[],[f130,f151])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.49    inference(resolution,[],[f70,f53])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK1) | v1_tops_2(u1_pre_topc(sK1),X0)) )),
% 0.20/0.49    inference(resolution,[],[f135,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    v1_tops_2(u1_pre_topc(sK1),sK1)),
% 0.20/0.49    inference(resolution,[],[f59,f54])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | v1_tops_2(u1_pre_topc(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~v1_tops_2(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X3,sK1) | v1_tops_2(X2,X3)) )),
% 0.20/0.49    inference(resolution,[],[f86,f54])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | v1_tops_2(X3,X2)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f83,f70])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK1),sK0) | ~r2_hidden(X0,u1_pre_topc(sK1)) | v3_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f204,f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~r2_hidden(X0,X1) | v3_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f147,f82])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f73,f53])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X3,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    ~v3_pre_topc(sK2(sK1),sK0)),
% 0.20/0.49    inference(resolution,[],[f379,f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~v3_pre_topc(sK2(sK1),sK0)),
% 0.20/0.49    inference(resolution,[],[f171,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_pre_topc(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f71,f53])).
% 0.20/0.49  fof(f379,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f378,f53])).
% 0.20/0.49  fof(f378,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f377,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    v3_tdlat_3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f377,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f376,f171])).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f369,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X2,X0] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f362,f312])).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | v3_pre_topc(X0,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f311,f53])).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f309,f283])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f282,f53])).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    v1_tops_2(u1_pre_topc(sK0),sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f246,f60])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f239,f151])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_pre_topc(sK1,sK0) | v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.20/0.49    inference(superposition,[],[f190,f218])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | v1_tops_2(u1_pre_topc(sK0),X0)) )),
% 0.20/0.49    inference(resolution,[],[f134,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.20/0.49    inference(resolution,[],[f59,f53])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,sK0) | v1_tops_2(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f86,f53])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK0),sK1) | ~r2_hidden(X0,u1_pre_topc(sK0)) | v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f226,f60])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X3,sK1) | ~r2_hidden(X4,X3) | v3_pre_topc(X4,sK1)) )),
% 0.20/0.49    inference(superposition,[],[f150,f218])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~v1_tops_2(X3,sK1) | ~r2_hidden(X2,X3) | v3_pre_topc(X2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f148,f82])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_tops_2(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v3_pre_topc(X2,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f73,f54])).
% 0.20/0.49  fof(f362,plain,(
% 0.20/0.49    ~v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1) | ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 0.20/0.49    inference(resolution,[],[f287,f242])).
% 0.20/0.49  % (15136)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f241,f54])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f233,f57])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(superposition,[],[f64,f218])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    ( ! [X1] : (r2_hidden(X1,u1_pre_topc(sK1)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X1,u1_pre_topc(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f224,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,u1_pre_topc(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f96,f53])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (15140)------------------------------
% 0.20/0.49  % (15140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15140)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (15140)Memory used [KB]: 1791
% 0.20/0.49  % (15140)Time elapsed: 0.083 s
% 0.20/0.49  % (15140)------------------------------
% 0.20/0.49  % (15140)------------------------------
% 0.20/0.49  % (15133)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (15129)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (15123)Success in time 0.149 s
%------------------------------------------------------------------------------

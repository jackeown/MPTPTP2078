%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1276+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:37 EST 2020

% Result     : Theorem 26.76s
% Output     : Refutation 26.76s
% Verified   : 
% Statistics : Number of formulae       :  256 (1468 expanded)
%              Number of leaves         :   38 ( 446 expanded)
%              Depth                    :   32
%              Number of atoms          :  827 (6291 expanded)
%              Number of equality atoms :   74 ( 206 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14492,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2770,f14490])).

fof(f14490,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f2529,f14226,f14342])).

fof(f14342,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f14341,f100])).

fof(f100,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f85,f84])).

fof(f84,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ? [X1] :
        ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).

fof(f14341,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f14336,f282])).

fof(f282,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f235,f99])).

fof(f99,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f235,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f100,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f14336,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f7785,f1250])).

fof(f1250,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_xboole_0(X15,k1_tops_1(sK0,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X16,k1_tops_1(sK0,X14))
      | ~ r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1249,f174])).

fof(f174,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X23),sK0) ) ),
    inference(subsumption_resolution,[],[f159,f99])).

fof(f159,plain,(
    ! [X23] :
      ( v3_pre_topc(k1_tops_1(sK0,X23),sK0)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f98,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f98,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f1249,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X15,k1_tops_1(sK0,X14))
      | ~ r2_hidden(X16,k1_tops_1(sK0,X14))
      | ~ v3_pre_topc(k1_tops_1(sK0,X14),sK0)
      | ~ r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1248,f1065])).

fof(f1065,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X53,k2_pre_topc(sK0,X52))
      | m1_subset_1(X53,u1_struct_0(sK0))
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f199,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f199,plain,(
    ! [X37] :
      ( m1_subset_1(k2_pre_topc(sK0,X37),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f99,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1248,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X15,k1_tops_1(sK0,X14))
      | ~ r2_hidden(X16,k1_tops_1(sK0,X14))
      | ~ v3_pre_topc(k1_tops_1(sK0,X14),sK0)
      | ~ r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1247,f544])).

fof(f544,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f297,f538])).

fof(f538,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f501,f296])).

fof(f296,plain,(
    ~ v1_xboole_0(k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f295,f98])).

fof(f295,plain,
    ( ~ v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f294,f99])).

fof(f294,plain,
    ( ~ v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f289,f282])).

fof(f289,plain,
    ( ~ v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f102,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tops_1)).

fof(f102,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f501,plain,
    ( v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f282,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f297,plain,
    ( ~ v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f176,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f176,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f99,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1247,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X15,k1_tops_1(sK0,X14))
      | ~ r2_hidden(X16,k1_tops_1(sK0,X14))
      | ~ v3_pre_topc(k1_tops_1(sK0,X14),sK0)
      | ~ r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1246,f98])).

fof(f1246,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X15,k1_tops_1(sK0,X14))
      | ~ r2_hidden(X16,k1_tops_1(sK0,X14))
      | ~ v3_pre_topc(k1_tops_1(sK0,X14),sK0)
      | ~ r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1203,f99])).

fof(f1203,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X15,k1_tops_1(sK0,X14))
      | ~ r2_hidden(X16,k1_tops_1(sK0,X14))
      | ~ v3_pre_topc(k1_tops_1(sK0,X14),sK0)
      | ~ r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f201,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK2(X0,X1,X2))
                    & r2_hidden(X2,sK2(X0,X1,X2))
                    & v3_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK2(X0,X1,X2))
        & r2_hidden(X2,sK2(X0,X1,X2))
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

fof(f201,plain,(
    ! [X39] :
      ( m1_subset_1(k1_tops_1(sK0,X39),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f99,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f7785,plain,(
    r1_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f4418,f7783])).

fof(f7783,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3329,f7780])).

fof(f7780,plain,(
    v2_tops_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f3322,f7779])).

fof(f7779,plain,(
    v3_tops_1(k1_xboole_0,sK0) ),
    inference(global_subsumption,[],[f3321,f7776])).

fof(f7776,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f7431,f103])).

fof(f103,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f7431,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f7430,f3372])).

fof(f3372,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f1979,f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f1979,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f703,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f703,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f287,f126])).

fof(f126,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f287,plain,(
    ! [X20] : m1_subset_1(k3_xboole_0(X20,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f240,f239])).

fof(f239,plain,(
    ! [X19] : k9_subset_1(u1_struct_0(sK0),X19,sK1) = k3_xboole_0(X19,sK1) ),
    inference(resolution,[],[f100,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f240,plain,(
    ! [X20] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X20,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f100,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f7430,plain,(
    ! [X5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f7429,f3415])).

fof(f3415,plain,(
    ! [X0] :
      ( v2_tops_1(X0,sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f3414,f3372])).

fof(f3414,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3413,f98])).

fof(f3413,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f3408,f99])).

fof(f3408,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f3407,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tops_1)).

fof(f3407,plain,(
    ! [X17] :
      ( v3_tops_1(X17,sK0)
      | ~ v1_xboole_0(X17) ) ),
    inference(subsumption_resolution,[],[f169,f3372])).

fof(f169,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X17)
      | v3_tops_1(X17,sK0) ) ),
    inference(subsumption_resolution,[],[f154,f99])).

fof(f154,plain,(
    ! [X17] :
      ( v3_tops_1(X17,sK0)
      | ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f98,f121])).

fof(f7429,plain,(
    ! [X5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X5)
      | ~ v2_tops_1(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f7427,f99])).

fof(f7427,plain,(
    ! [X5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X5)
      | ~ v2_tops_1(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f3427,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f3427,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(sK0,X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f3426,f3372])).

fof(f3426,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3416,f99])).

fof(f3416,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f3415,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_tops_1(X1,X0)
        & l1_pre_topc(X0) )
     => v1_xboole_0(k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_tops_1)).

fof(f3321,plain,
    ( v3_tops_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f1979,f169])).

fof(f3322,plain,
    ( ~ v3_tops_1(k1_xboole_0,sK0)
    | v2_tops_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f1979,f170])).

fof(f170,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tops_1(X18,sK0)
      | v2_tops_1(X18,sK0) ) ),
    inference(subsumption_resolution,[],[f155,f99])).

fof(f155,plain,(
    ! [X18] :
      ( v2_tops_1(X18,sK0)
      | ~ v3_tops_1(X18,sK0)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f98,f122])).

fof(f3329,plain,
    ( ~ v2_tops_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f1979,f180])).

fof(f180,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X3,sK0)
      | k1_xboole_0 = k1_tops_1(sK0,X3) ) ),
    inference(resolution,[],[f99,f109])).

fof(f4418,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | r1_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f138,f1564])).

fof(f1564,plain,(
    k1_tops_1(sK0,k1_xboole_0) = k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1563,f1396])).

fof(f1396,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f355,f1384])).

fof(f1384,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1383,f98])).

fof(f1383,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1363,f99])).

fof(f1363,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f206,f287])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f205,f99])).

fof(f205,plain,(
    ! [X0,X1] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f203,f100])).

fof(f203,plain,(
    ! [X0,X1] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f101,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f101,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f355,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f246,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f246,plain,(
    r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f211,f99])).

fof(f211,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f100,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f1563,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1547,f126])).

fof(f1547,plain,(
    k1_tops_1(sK0,k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f1446,f282])).

fof(f1446,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,k3_xboole_0(X17,sK1)) = k3_xboole_0(sK1,k1_tops_1(sK0,X17)) ) ),
    inference(forward_demodulation,[],[f1425,f126])).

fof(f1425,plain,(
    ! [X17] :
      ( k1_tops_1(sK0,k3_xboole_0(X17,sK1)) = k3_xboole_0(k1_tops_1(sK0,X17),sK1)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f662,f1384])).

fof(f662,plain,(
    ! [X17] :
      ( k1_tops_1(sK0,k3_xboole_0(X17,sK1)) = k3_xboole_0(k1_tops_1(sK0,X17),k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f286,f600])).

fof(f600,plain,(
    ! [X19] : k9_subset_1(u1_struct_0(sK0),X19,k1_tops_1(sK0,sK1)) = k3_xboole_0(X19,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f283,f145])).

fof(f283,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f236,f99])).

fof(f236,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f100,f135])).

fof(f286,plain,(
    ! [X17] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X17),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(X17,sK1))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f273,f239])).

fof(f273,plain,(
    ! [X17] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X17),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X17,sK1))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f272,f98])).

fof(f272,plain,(
    ! [X17] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X17),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X17,sK1))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f99])).

fof(f229,plain,(
    ! [X17] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X17),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X17,sK1))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f100,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tops_1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f92])).

fof(f14226,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X5,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f6141,f139])).

fof(f139,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f94,f95])).

fof(f95,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f6141,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f125,f1516])).

fof(f1516,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f1513,f834])).

fof(f834,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f779,f99])).

fof(f779,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f242,f133])).

fof(f242,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f100,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1513,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f247,f145])).

fof(f247,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f212,f99])).

fof(f212,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f100,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f125,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2529,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f503,f139])).

fof(f503,plain,(
    r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f468,f99])).

fof(f468,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f282,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2770,plain,(
    r2_hidden(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f861,f2769])).

fof(f2769,plain,(
    ~ v1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2709,f2767])).

fof(f2767,plain,(
    ~ v3_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f2710,f2766])).

fof(f2766,plain,(
    ~ v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f2765,f348])).

fof(f348,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f347,f99])).

fof(f347,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f346,f282])).

fof(f346,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f293,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f293,plain,(
    ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f292,f98])).

fof(f292,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f291,f99])).

fof(f291,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f290,f282])).

fof(f290,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f288,f275])).

fof(f275,plain,(
    v4_pre_topc(k2_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f274,f98])).

fof(f274,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f230,f99])).

fof(f230,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f100,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

fof(f288,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f102,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tops_1(X1,X0)
              & v4_pre_topc(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tops_1)).

fof(f2765,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f2717,f535])).

fof(f535,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f495,f99])).

fof(f495,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f282,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f2717,plain,
    ( ~ v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f534,f180])).

fof(f534,plain,(
    m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f494,f99])).

fof(f494,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f282,f135])).

fof(f2710,plain,
    ( ~ v3_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(resolution,[],[f534,f170])).

fof(f2709,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | v3_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(resolution,[],[f534,f169])).

fof(f861,plain,
    ( r2_hidden(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | v1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f279,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f279,plain,(
    m1_subset_1(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f278,f98])).

fof(f278,plain,
    ( m1_subset_1(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f232,f99])).

fof(f232,plain,
    ( m1_subset_1(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f100,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_tops_1)).

%------------------------------------------------------------------------------

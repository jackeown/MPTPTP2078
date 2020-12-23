%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:16 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  235 (15588 expanded)
%              Number of leaves         :   17 (2764 expanded)
%              Depth                    :   39
%              Number of atoms          : 1345 (124742 expanded)
%              Number of equality atoms :   95 (9176 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1693,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1692,f1691])).

fof(f1691,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1558,f1690])).

fof(f1690,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1689,f1571])).

fof(f1571,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f1554,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1554,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1535,f54])).

fof(f54,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f1535,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1162,f1516])).

fof(f1516,plain,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1515,f456])).

fof(f456,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f285,f184])).

fof(f184,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f115,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f115,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f94,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f285,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f284,f103])).

fof(f103,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f101,f59])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f89,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f56,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

% (27482)Refutation not found, incomplete strategy% (27482)------------------------------
% (27482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27482)Termination reason: Refutation not found, incomplete strategy

% (27482)Memory used [KB]: 6140
% (27482)Time elapsed: 0.277 s
% (27482)------------------------------
% (27482)------------------------------
fof(f284,plain,(
    ! [X9] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f283,f184])).

fof(f283,plain,(
    ! [X9] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f282,f97])).

fof(f97,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f96,f57])).

fof(f96,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f59])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f58])).

fof(f87,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f56,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f282,plain,(
    ! [X9] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f239,f85])).

fof(f85,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f59,f82])).

fof(f239,plain,(
    ! [X9] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f100,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f100,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f99,f57])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f59])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f88,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f56,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1515,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f1514,f1508])).

fof(f1508,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1507,f850])).

fof(f850,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f293,f185])).

fof(f185,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f115,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f293,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f292,f103])).

fof(f292,plain,(
    ! [X10] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f291,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f291,plain,(
    ! [X10] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f290,f97])).

fof(f290,plain,(
    ! [X10] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f289,f59])).

fof(f289,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f288,f58])).

fof(f288,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f287,f57])).

fof(f287,plain,(
    ! [X10] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f286,f115])).

fof(f286,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f240,f114])).

fof(f114,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f93,f59])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f240,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(resolution,[],[f100,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f1507,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f1030,f185])).

fof(f1030,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1029,f57])).

fof(f1029,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1028,f58])).

fof(f1028,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1026,f59])).

fof(f1026,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f299,f56])).

fof(f299,plain,(
    ! [X12,X11] :
      ( ~ m1_pre_topc(sK1,X11)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f298,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f298,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f297,f103])).

fof(f297,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f296,f97])).

fof(f296,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f295,f59])).

fof(f295,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f294,f58])).

fof(f294,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f241,f57])).

fof(f241,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(resolution,[],[f100,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f1514,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f1513,f447])).

fof(f447,plain,(
    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f281,f184])).

fof(f281,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f280,f103])).

fof(f280,plain,(
    ! [X8] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f279,f184])).

fof(f279,plain,(
    ! [X8] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f278,f97])).

fof(f278,plain,(
    ! [X8] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f238,f85])).

fof(f238,plain,(
    ! [X8] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f100,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1513,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1512,f1508])).

fof(f1512,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f1511,f440])).

fof(f440,plain,(
    v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f277,f184])).

fof(f277,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f276,f103])).

fof(f276,plain,(
    ! [X7] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f275,f184])).

fof(f275,plain,(
    ! [X7] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f274,f97])).

fof(f274,plain,(
    ! [X7] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f237,f85])).

fof(f237,plain,(
    ! [X7] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(resolution,[],[f100,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1511,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1509,f1508])).

fof(f1509,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f1393,f1508])).

fof(f1393,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1392,f97])).

fof(f1392,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1391,f103])).

fof(f1391,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1390,f100])).

fof(f1390,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f1002,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f1002,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1001,f57])).

fof(f1001,plain,
    ( v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1000,f58])).

fof(f1000,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f998,f59])).

fof(f998,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f273,f56])).

fof(f273,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f272,f103])).

fof(f272,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f271,f97])).

fof(f271,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f270,f55])).

fof(f270,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f269,f59])).

fof(f269,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f268,f58])).

fof(f268,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f236,f57])).

fof(f236,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f100,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f1162,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1161,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f1161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1160,f55])).

fof(f1160,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1159,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f1159,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1150,f185])).

fof(f1150,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f259,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f259,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f258,f103])).

fof(f258,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f257,f57])).

fof(f257,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f256,f97])).

fof(f256,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f255,f115])).

fof(f255,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f254,f114])).

fof(f254,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f253,f55])).

fof(f253,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f252,f59])).

fof(f252,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f234,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(resolution,[],[f100,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f1689,plain,
    ( sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1565,f1688])).

fof(f1688,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1686,f1554])).

fof(f1686,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1568,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f106,f57])).

fof(f106,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f55])).

fof(f105,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f104,f59])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f90,f58])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f56,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f1568,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1553,f110])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f109,f57])).

fof(f109,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f108,f55])).

fof(f108,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f59])).

fof(f91,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f1553,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1532,f54])).

fof(f1532,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1128,f1516])).

fof(f1128,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1127,f53])).

fof(f1127,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1126,f55])).

fof(f1126,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1125,f51])).

fof(f1125,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1116,f185])).

fof(f1116,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f251,f52])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f250,f103])).

fof(f250,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f249,f57])).

fof(f249,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f248,f97])).

fof(f248,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f247,f115])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f246,f114])).

fof(f246,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f245,f55])).

fof(f245,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f244,f59])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f233,f58])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(resolution,[],[f100,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1565,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1553,f301])).

fof(f301,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(subsumption_resolution,[],[f300,f103])).

fof(f300,plain,(
    ! [X13] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(subsumption_resolution,[],[f242,f97])).

fof(f242,plain,(
    ! [X13] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(resolution,[],[f100,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f1558,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1542,f54])).

fof(f1542,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1322,f1516])).

fof(f1322,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1321,f53])).

fof(f1321,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1320,f55])).

fof(f1320,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1319,f51])).

fof(f1319,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1310,f185])).

fof(f1310,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f267,f52])).

fof(f267,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f266,f103])).

fof(f266,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f265,f57])).

fof(f265,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f264,f97])).

fof(f264,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f263,f115])).

fof(f263,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f262,f114])).

fof(f262,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f261,f55])).

fof(f261,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f260,f59])).

fof(f260,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f235,f58])).

fof(f235,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1692,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1687,f1554])).

fof(f1687,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1568,f50])).

fof(f50,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:35:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (27484)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (27492)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (27473)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (27473)Refutation not found, incomplete strategy% (27473)------------------------------
% 0.20/0.50  % (27473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27473)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27473)Memory used [KB]: 10618
% 0.20/0.50  % (27473)Time elapsed: 0.082 s
% 0.20/0.50  % (27473)------------------------------
% 0.20/0.50  % (27473)------------------------------
% 0.20/0.50  % (27475)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (27493)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (27485)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (27480)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (27482)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (27489)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (27474)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (27483)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (27490)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.38/0.53  % (27496)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.38/0.53  % (27476)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.38/0.53  % (27481)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.54  % (27488)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.38/0.54  % (27477)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.38/0.54  % (27478)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.38/0.54  % (27479)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.38/0.54  % (27495)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.51/0.55  % (27494)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.51/0.55  % (27497)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.51/0.55  % (27487)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.51/0.56  % (27486)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.51/0.56  % (27491)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.51/0.56  % (27498)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.13/0.66  % (27478)Refutation found. Thanks to Tanya!
% 2.13/0.66  % SZS status Theorem for theBenchmark
% 2.13/0.66  % SZS output start Proof for theBenchmark
% 2.13/0.66  fof(f1693,plain,(
% 2.13/0.66    $false),
% 2.13/0.66    inference(subsumption_resolution,[],[f1692,f1691])).
% 2.13/0.66  fof(f1691,plain,(
% 2.13/0.66    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.13/0.66    inference(backward_demodulation,[],[f1558,f1690])).
% 2.13/0.66  fof(f1690,plain,(
% 2.13/0.66    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.13/0.66    inference(subsumption_resolution,[],[f1689,f1571])).
% 2.13/0.66  fof(f1571,plain,(
% 2.13/0.66    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.13/0.66    inference(resolution,[],[f1554,f71])).
% 2.13/0.66  fof(f71,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f34])).
% 2.13/0.66  fof(f34,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f19])).
% 2.13/0.66  fof(f19,plain,(
% 2.13/0.66    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.13/0.66    inference(unused_predicate_definition_removal,[],[f1])).
% 2.13/0.66  fof(f1,axiom,(
% 2.13/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.13/0.66  fof(f1554,plain,(
% 2.13/0.66    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.13/0.66    inference(subsumption_resolution,[],[f1535,f54])).
% 2.13/0.66  fof(f54,plain,(
% 2.13/0.66    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f21,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f20])).
% 2.13/0.66  fof(f20,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f18])).
% 2.13/0.66  fof(f18,negated_conjecture,(
% 2.13/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.13/0.66    inference(negated_conjecture,[],[f17])).
% 2.13/0.66  fof(f17,conjecture,(
% 2.13/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.13/0.66  fof(f1535,plain,(
% 2.13/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.13/0.66    inference(backward_demodulation,[],[f1162,f1516])).
% 2.13/0.66  fof(f1516,plain,(
% 2.13/0.66    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1515,f456])).
% 2.13/0.66  fof(f456,plain,(
% 2.13/0.66    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.13/0.66    inference(resolution,[],[f285,f184])).
% 2.13/0.66  fof(f184,plain,(
% 2.13/0.66    l1_struct_0(sK1)),
% 2.13/0.66    inference(resolution,[],[f115,f82])).
% 2.13/0.66  fof(f82,plain,(
% 2.13/0.66    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f49])).
% 2.13/0.66  fof(f49,plain,(
% 2.13/0.66    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f5])).
% 2.13/0.66  fof(f5,axiom,(
% 2.13/0.66    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.13/0.66  fof(f115,plain,(
% 2.13/0.66    l1_pre_topc(sK1)),
% 2.13/0.66    inference(subsumption_resolution,[],[f94,f59])).
% 2.13/0.66  fof(f59,plain,(
% 2.13/0.66    l1_pre_topc(sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f94,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 2.13/0.66    inference(resolution,[],[f56,f75])).
% 2.13/0.66  fof(f75,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f41])).
% 2.13/0.66  fof(f41,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f6])).
% 2.13/0.66  fof(f6,axiom,(
% 2.13/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.13/0.66  fof(f56,plain,(
% 2.13/0.66    m1_pre_topc(sK1,sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f285,plain,(
% 2.13/0.66    ( ! [X9] : (~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f284,f103])).
% 2.13/0.66  fof(f103,plain,(
% 2.13/0.66    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.13/0.66    inference(subsumption_resolution,[],[f102,f57])).
% 2.13/0.66  fof(f57,plain,(
% 2.13/0.66    ~v2_struct_0(sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f102,plain,(
% 2.13/0.66    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.13/0.66    inference(subsumption_resolution,[],[f101,f59])).
% 2.13/0.66  fof(f101,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.13/0.66    inference(subsumption_resolution,[],[f89,f58])).
% 2.13/0.66  fof(f58,plain,(
% 2.13/0.66    v2_pre_topc(sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f89,plain,(
% 2.13/0.66    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.13/0.66    inference(resolution,[],[f56,f68])).
% 2.13/0.66  fof(f68,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f29])).
% 2.13/0.66  fof(f29,plain,(
% 2.13/0.66    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f28])).
% 2.13/0.66  fof(f28,plain,(
% 2.13/0.66    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f11])).
% 2.13/0.66  fof(f11,axiom,(
% 2.13/0.66    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.48/0.68  % (27482)Refutation not found, incomplete strategy% (27482)------------------------------
% 2.48/0.68  % (27482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.48/0.68  % (27482)Termination reason: Refutation not found, incomplete strategy
% 2.48/0.68  
% 2.48/0.68  % (27482)Memory used [KB]: 6140
% 2.48/0.68  % (27482)Time elapsed: 0.277 s
% 2.48/0.68  % (27482)------------------------------
% 2.48/0.68  % (27482)------------------------------
% 2.48/0.68  fof(f284,plain,(
% 2.48/0.68    ( ! [X9] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f283,f184])).
% 2.48/0.68  fof(f283,plain,(
% 2.48/0.68    ( ! [X9] : (~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f282,f97])).
% 2.48/0.68  fof(f97,plain,(
% 2.48/0.68    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f96,f57])).
% 2.48/0.68  fof(f96,plain,(
% 2.48/0.68    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f95,f59])).
% 2.48/0.68  fof(f95,plain,(
% 2.48/0.68    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f87,f58])).
% 2.48/0.68  fof(f87,plain,(
% 2.48/0.68    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(resolution,[],[f56,f66])).
% 2.48/0.68  fof(f66,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f29])).
% 2.48/0.68  fof(f282,plain,(
% 2.48/0.68    ( ! [X9] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f239,f85])).
% 2.48/0.68  fof(f85,plain,(
% 2.48/0.68    l1_struct_0(sK0)),
% 2.48/0.68    inference(resolution,[],[f59,f82])).
% 2.48/0.68  fof(f239,plain,(
% 2.48/0.68    ( ! [X9] : (~l1_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.48/0.68    inference(resolution,[],[f100,f79])).
% 2.48/0.68  fof(f79,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f44])).
% 2.48/0.68  fof(f44,plain,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f43])).
% 2.48/0.68  fof(f43,plain,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f10])).
% 2.48/0.68  fof(f10,axiom,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 2.48/0.68  fof(f100,plain,(
% 2.48/0.68    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.48/0.68    inference(subsumption_resolution,[],[f99,f57])).
% 2.48/0.68  fof(f99,plain,(
% 2.48/0.68    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.48/0.68    inference(subsumption_resolution,[],[f98,f59])).
% 2.48/0.68  fof(f98,plain,(
% 2.48/0.68    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.48/0.68    inference(subsumption_resolution,[],[f88,f58])).
% 2.48/0.68  fof(f88,plain,(
% 2.48/0.68    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.48/0.68    inference(resolution,[],[f56,f67])).
% 2.48/0.68  fof(f67,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f29])).
% 2.48/0.68  fof(f1515,plain,(
% 2.48/0.68    ~m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 2.48/0.68    inference(forward_demodulation,[],[f1514,f1508])).
% 2.48/0.68  fof(f1508,plain,(
% 2.48/0.68    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(forward_demodulation,[],[f1507,f850])).
% 2.48/0.68  fof(f850,plain,(
% 2.48/0.68    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1))),
% 2.48/0.68    inference(resolution,[],[f293,f185])).
% 2.48/0.68  fof(f185,plain,(
% 2.48/0.68    m1_pre_topc(sK1,sK1)),
% 2.48/0.68    inference(resolution,[],[f115,f76])).
% 2.48/0.68  fof(f76,plain,(
% 2.48/0.68    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f42])).
% 2.48/0.68  fof(f42,plain,(
% 2.48/0.68    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.48/0.68    inference(ennf_transformation,[],[f12])).
% 2.48/0.68  fof(f12,axiom,(
% 2.48/0.68    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.48/0.68  fof(f293,plain,(
% 2.48/0.68    ( ! [X10] : (~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f292,f103])).
% 2.48/0.68  fof(f292,plain,(
% 2.48/0.68    ( ! [X10] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f291,f55])).
% 2.48/0.68  fof(f55,plain,(
% 2.48/0.68    ~v2_struct_0(sK1)),
% 2.48/0.68    inference(cnf_transformation,[],[f21])).
% 2.48/0.68  fof(f291,plain,(
% 2.48/0.68    ( ! [X10] : (v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f290,f97])).
% 2.48/0.68  fof(f290,plain,(
% 2.48/0.68    ( ! [X10] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f289,f59])).
% 2.48/0.68  fof(f289,plain,(
% 2.48/0.68    ( ! [X10] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f288,f58])).
% 2.48/0.68  fof(f288,plain,(
% 2.48/0.68    ( ! [X10] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f287,f57])).
% 2.48/0.68  fof(f287,plain,(
% 2.48/0.68    ( ! [X10] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f286,f115])).
% 2.48/0.68  fof(f286,plain,(
% 2.48/0.68    ( ! [X10] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f240,f114])).
% 2.48/0.68  fof(f114,plain,(
% 2.48/0.68    v2_pre_topc(sK1)),
% 2.48/0.68    inference(subsumption_resolution,[],[f113,f58])).
% 2.48/0.68  fof(f113,plain,(
% 2.48/0.68    ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.48/0.68    inference(subsumption_resolution,[],[f93,f59])).
% 2.48/0.68  fof(f93,plain,(
% 2.48/0.68    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.48/0.68    inference(resolution,[],[f56,f74])).
% 2.48/0.68  fof(f74,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f40])).
% 2.48/0.68  fof(f40,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/0.68    inference(flattening,[],[f39])).
% 2.48/0.68  fof(f39,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f4])).
% 2.48/0.68  fof(f4,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.48/0.68  fof(f240,plain,(
% 2.48/0.68    ( ! [X10] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.48/0.68    inference(resolution,[],[f100,f80])).
% 2.48/0.68  fof(f80,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f46])).
% 2.48/0.68  fof(f46,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f45])).
% 2.48/0.68  fof(f45,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f8])).
% 2.48/0.68  fof(f8,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.48/0.68  fof(f1507,plain,(
% 2.48/0.68    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(resolution,[],[f1030,f185])).
% 2.48/0.68  fof(f1030,plain,(
% 2.48/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f1029,f57])).
% 2.48/0.68  fof(f1029,plain,(
% 2.48/0.68    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f1028,f58])).
% 2.48/0.68  fof(f1028,plain,(
% 2.48/0.68    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f1026,f59])).
% 2.48/0.68  fof(f1026,plain,(
% 2.48/0.68    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.48/0.68    inference(resolution,[],[f299,f56])).
% 2.48/0.68  fof(f299,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~m1_pre_topc(sK1,X11) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f298,f73])).
% 2.48/0.68  fof(f73,plain,(
% 2.48/0.68    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f38])).
% 2.48/0.68  fof(f38,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/0.68    inference(flattening,[],[f37])).
% 2.48/0.68  fof(f37,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f15])).
% 2.48/0.68  fof(f15,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.48/0.68  fof(f298,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | v2_struct_0(X11) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f297,f103])).
% 2.48/0.68  fof(f297,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f296,f97])).
% 2.48/0.68  fof(f296,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f295,f59])).
% 2.48/0.68  fof(f295,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f294,f58])).
% 2.48/0.68  fof(f294,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f241,f57])).
% 2.48/0.68  fof(f241,plain,(
% 2.48/0.68    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.48/0.68    inference(resolution,[],[f100,f81])).
% 2.48/0.68  fof(f81,plain,(
% 2.48/0.68    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f48])).
% 2.48/0.68  fof(f48,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f47])).
% 2.48/0.68  fof(f47,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f9])).
% 2.48/0.68  fof(f9,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.48/0.68  fof(f1514,plain,(
% 2.48/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1513,f447])).
% 2.48/0.68  fof(f447,plain,(
% 2.48/0.68    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.48/0.68    inference(resolution,[],[f281,f184])).
% 2.48/0.68  fof(f281,plain,(
% 2.48/0.68    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f280,f103])).
% 2.48/0.68  fof(f280,plain,(
% 2.48/0.68    ( ! [X8] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f279,f184])).
% 2.48/0.68  fof(f279,plain,(
% 2.48/0.68    ( ! [X8] : (~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f278,f97])).
% 2.48/0.68  fof(f278,plain,(
% 2.48/0.68    ( ! [X8] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f238,f85])).
% 2.48/0.68  fof(f238,plain,(
% 2.48/0.68    ( ! [X8] : (~l1_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.48/0.68    inference(resolution,[],[f100,f78])).
% 2.48/0.68  fof(f78,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f44])).
% 2.48/0.68  fof(f1513,plain,(
% 2.48/0.68    ~v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.48/0.68    inference(forward_demodulation,[],[f1512,f1508])).
% 2.48/0.68  fof(f1512,plain,(
% 2.48/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1511,f440])).
% 2.48/0.68  fof(f440,plain,(
% 2.48/0.68    v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1))),
% 2.48/0.68    inference(resolution,[],[f277,f184])).
% 2.48/0.68  fof(f277,plain,(
% 2.48/0.68    ( ! [X7] : (~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f276,f103])).
% 2.48/0.68  fof(f276,plain,(
% 2.48/0.68    ( ! [X7] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f275,f184])).
% 2.48/0.68  fof(f275,plain,(
% 2.48/0.68    ( ! [X7] : (~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f274,f97])).
% 2.48/0.68  fof(f274,plain,(
% 2.48/0.68    ( ! [X7] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f237,f85])).
% 2.48/0.68  fof(f237,plain,(
% 2.48/0.68    ( ! [X7] : (~l1_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.48/0.68    inference(resolution,[],[f100,f77])).
% 2.48/0.68  fof(f77,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f44])).
% 2.48/0.68  fof(f1511,plain,(
% 2.48/0.68    ~v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.48/0.68    inference(forward_demodulation,[],[f1509,f1508])).
% 2.48/0.68  fof(f1509,plain,(
% 2.48/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.48/0.68    inference(backward_demodulation,[],[f1393,f1508])).
% 2.48/0.68  fof(f1393,plain,(
% 2.48/0.68    ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1392,f97])).
% 2.48/0.68  fof(f1392,plain,(
% 2.48/0.68    ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1391,f103])).
% 2.48/0.68  fof(f1391,plain,(
% 2.48/0.68    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1390,f100])).
% 2.48/0.68  fof(f1390,plain,(
% 2.48/0.68    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.48/0.68    inference(resolution,[],[f1002,f61])).
% 2.48/0.68  fof(f61,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~v1_funct_1(X2)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f23])).
% 2.48/0.68  fof(f23,plain,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.48/0.68    inference(flattening,[],[f22])).
% 2.48/0.68  fof(f22,plain,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.48/0.68    inference(ennf_transformation,[],[f3])).
% 2.48/0.68  fof(f3,axiom,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.48/0.68  fof(f1002,plain,(
% 2.48/0.68    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1001,f57])).
% 2.48/0.68  fof(f1001,plain,(
% 2.48/0.68    v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1000,f58])).
% 2.48/0.68  fof(f1000,plain,(
% 2.48/0.68    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.48/0.68    inference(subsumption_resolution,[],[f998,f59])).
% 2.48/0.68  fof(f998,plain,(
% 2.48/0.68    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.48/0.68    inference(resolution,[],[f273,f56])).
% 2.48/0.68  fof(f273,plain,(
% 2.48/0.68    ( ! [X6] : (~m1_pre_topc(sK1,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f272,f103])).
% 2.48/0.68  fof(f272,plain,(
% 2.48/0.68    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f271,f97])).
% 2.48/0.68  fof(f271,plain,(
% 2.48/0.68    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f270,f55])).
% 2.48/0.68  fof(f270,plain,(
% 2.48/0.68    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f269,f59])).
% 2.48/0.68  fof(f269,plain,(
% 2.48/0.68    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f268,f58])).
% 2.48/0.68  fof(f268,plain,(
% 2.48/0.68    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f236,f57])).
% 2.48/0.68  fof(f236,plain,(
% 2.48/0.68    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.48/0.68    inference(resolution,[],[f100,f65])).
% 2.48/0.68  fof(f65,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f27])).
% 2.48/0.68  fof(f27,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f26])).
% 2.48/0.68  fof(f26,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f14])).
% 2.48/0.68  fof(f14,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.48/0.68  fof(f1162,plain,(
% 2.48/0.68    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1161,f53])).
% 2.48/0.68  fof(f53,plain,(
% 2.48/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.48/0.68    inference(cnf_transformation,[],[f21])).
% 2.48/0.68  fof(f1161,plain,(
% 2.48/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1160,f55])).
% 2.48/0.68  fof(f1160,plain,(
% 2.48/0.68    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1159,f51])).
% 2.48/0.68  fof(f51,plain,(
% 2.48/0.68    v1_funct_1(sK2)),
% 2.48/0.68    inference(cnf_transformation,[],[f21])).
% 2.48/0.68  fof(f1159,plain,(
% 2.48/0.68    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1150,f185])).
% 2.48/0.68  fof(f1150,plain,(
% 2.48/0.68    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(resolution,[],[f259,f52])).
% 2.48/0.68  fof(f52,plain,(
% 2.48/0.68    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.48/0.68    inference(cnf_transformation,[],[f21])).
% 2.48/0.68  fof(f259,plain,(
% 2.48/0.68    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | v2_struct_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f258,f103])).
% 2.48/0.68  fof(f258,plain,(
% 2.48/0.68    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f257,f57])).
% 2.48/0.68  fof(f257,plain,(
% 2.48/0.68    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f256,f97])).
% 2.48/0.68  fof(f256,plain,(
% 2.48/0.68    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f255,f115])).
% 2.48/0.68  fof(f255,plain,(
% 2.48/0.68    ( ! [X2,X3] : (~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f254,f114])).
% 2.48/0.68  fof(f254,plain,(
% 2.48/0.68    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f253,f55])).
% 2.48/0.68  fof(f253,plain,(
% 2.48/0.68    ( ! [X2,X3] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f252,f59])).
% 2.48/0.68  fof(f252,plain,(
% 2.48/0.68    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f234,f58])).
% 2.48/0.68  fof(f234,plain,(
% 2.48/0.68    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.48/0.68    inference(resolution,[],[f100,f63])).
% 2.48/0.68  fof(f63,plain,(
% 2.48/0.68    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f25])).
% 2.48/0.68  fof(f25,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f24])).
% 2.48/0.68  fof(f24,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f13])).
% 2.48/0.68  fof(f13,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.48/0.68  fof(f1689,plain,(
% 2.48/0.68    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 2.48/0.68    inference(backward_demodulation,[],[f1565,f1688])).
% 2.48/0.68  fof(f1688,plain,(
% 2.48/0.68    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1686,f1554])).
% 2.48/0.68  fof(f1686,plain,(
% 2.48/0.68    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(resolution,[],[f1568,f107])).
% 2.48/0.68  fof(f107,plain,(
% 2.48/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f106,f57])).
% 2.48/0.68  fof(f106,plain,(
% 2.48/0.68    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f105,f55])).
% 2.48/0.68  fof(f105,plain,(
% 2.48/0.68    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f104,f59])).
% 2.48/0.68  fof(f104,plain,(
% 2.48/0.68    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f90,f58])).
% 2.48/0.68  fof(f90,plain,(
% 2.48/0.68    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.48/0.68    inference(resolution,[],[f56,f69])).
% 2.48/0.68  fof(f69,plain,(
% 2.48/0.68    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 2.48/0.68    inference(cnf_transformation,[],[f31])).
% 2.48/0.68  fof(f31,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f30])).
% 2.48/0.68  fof(f30,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f16])).
% 2.48/0.68  fof(f16,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.48/0.68  fof(f1568,plain,(
% 2.48/0.68    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))),
% 2.48/0.68    inference(resolution,[],[f1553,f110])).
% 2.48/0.68  fof(f110,plain,(
% 2.48/0.68    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f109,f57])).
% 2.48/0.68  fof(f109,plain,(
% 2.48/0.68    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f108,f55])).
% 2.48/0.68  fof(f108,plain,(
% 2.48/0.68    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f91,f59])).
% 2.48/0.68  fof(f91,plain,(
% 2.48/0.68    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.48/0.68    inference(resolution,[],[f56,f72])).
% 2.48/0.68  fof(f72,plain,(
% 2.48/0.68    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 2.48/0.68    inference(cnf_transformation,[],[f36])).
% 2.48/0.68  fof(f36,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.68    inference(flattening,[],[f35])).
% 2.48/0.68  fof(f35,plain,(
% 2.48/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f7])).
% 2.48/0.68  fof(f7,axiom,(
% 2.48/0.68    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 2.48/0.68  fof(f1553,plain,(
% 2.48/0.68    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1532,f54])).
% 2.48/0.68  fof(f1532,plain,(
% 2.48/0.68    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.48/0.68    inference(backward_demodulation,[],[f1128,f1516])).
% 2.48/0.68  fof(f1128,plain,(
% 2.48/0.68    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1127,f53])).
% 2.48/0.68  fof(f1127,plain,(
% 2.48/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1126,f55])).
% 2.48/0.68  fof(f1126,plain,(
% 2.48/0.68    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1125,f51])).
% 2.48/0.68  fof(f1125,plain,(
% 2.48/0.68    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1116,f185])).
% 2.48/0.68  fof(f1116,plain,(
% 2.48/0.68    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(resolution,[],[f251,f52])).
% 2.48/0.68  fof(f251,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(X1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f250,f103])).
% 2.48/0.68  fof(f250,plain,(
% 2.48/0.68    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f249,f57])).
% 2.48/0.68  fof(f249,plain,(
% 2.48/0.68    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f248,f97])).
% 2.48/0.68  fof(f248,plain,(
% 2.48/0.68    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f247,f115])).
% 2.48/0.68  fof(f247,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f246,f114])).
% 2.48/0.68  fof(f246,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f245,f55])).
% 2.48/0.68  fof(f245,plain,(
% 2.48/0.68    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f244,f59])).
% 2.48/0.68  fof(f244,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f233,f58])).
% 2.48/0.68  fof(f233,plain,(
% 2.48/0.68    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.48/0.68    inference(resolution,[],[f100,f62])).
% 2.48/0.68  fof(f62,plain,(
% 2.48/0.68    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f25])).
% 2.48/0.68  fof(f1565,plain,(
% 2.48/0.68    v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(resolution,[],[f1553,f301])).
% 2.48/0.68  fof(f301,plain,(
% 2.48/0.68    ( ! [X13] : (~m1_subset_1(X13,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f300,f103])).
% 2.48/0.68  fof(f300,plain,(
% 2.48/0.68    ( ! [X13] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X13,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f242,f97])).
% 2.48/0.68  fof(f242,plain,(
% 2.48/0.68    ( ! [X13] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X13,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.48/0.68    inference(resolution,[],[f100,f70])).
% 2.48/0.68  fof(f70,plain,(
% 2.48/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f33])).
% 2.48/0.68  fof(f33,plain,(
% 2.48/0.68    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.48/0.68    inference(flattening,[],[f32])).
% 2.48/0.68  fof(f32,plain,(
% 2.48/0.68    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.48/0.68    inference(ennf_transformation,[],[f2])).
% 2.48/0.68  fof(f2,axiom,(
% 2.48/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.48/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 2.48/0.68  fof(f1558,plain,(
% 2.48/0.68    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1542,f54])).
% 2.48/0.68  fof(f1542,plain,(
% 2.48/0.68    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(backward_demodulation,[],[f1322,f1516])).
% 2.48/0.68  fof(f1322,plain,(
% 2.48/0.68    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1321,f53])).
% 2.48/0.68  fof(f1321,plain,(
% 2.48/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1320,f55])).
% 2.48/0.68  fof(f1320,plain,(
% 2.48/0.68    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1319,f51])).
% 2.48/0.68  fof(f1319,plain,(
% 2.48/0.68    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(subsumption_resolution,[],[f1310,f185])).
% 2.48/0.68  fof(f1310,plain,(
% 2.48/0.68    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.48/0.68    inference(resolution,[],[f267,f52])).
% 2.48/0.68  fof(f267,plain,(
% 2.48/0.68    ( ! [X4,X5] : (~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(X5) | v2_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f266,f103])).
% 2.48/0.68  fof(f266,plain,(
% 2.48/0.68    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f265,f57])).
% 2.48/0.68  fof(f265,plain,(
% 2.48/0.68    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f264,f97])).
% 2.48/0.68  fof(f264,plain,(
% 2.48/0.68    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f263,f115])).
% 2.48/0.68  fof(f263,plain,(
% 2.48/0.68    ( ! [X4,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f262,f114])).
% 2.48/0.68  fof(f262,plain,(
% 2.48/0.68    ( ! [X4,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f261,f55])).
% 2.48/0.68  fof(f261,plain,(
% 2.48/0.68    ( ! [X4,X5] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f260,f59])).
% 2.48/0.68  fof(f260,plain,(
% 2.48/0.68    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(subsumption_resolution,[],[f235,f58])).
% 2.48/0.68  fof(f235,plain,(
% 2.48/0.68    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.48/0.68    inference(resolution,[],[f100,f64])).
% 2.48/0.68  fof(f64,plain,(
% 2.48/0.68    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.48/0.68    inference(cnf_transformation,[],[f25])).
% 2.48/0.68  fof(f1692,plain,(
% 2.48/0.68    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(subsumption_resolution,[],[f1687,f1554])).
% 2.48/0.68  fof(f1687,plain,(
% 2.48/0.68    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.48/0.68    inference(resolution,[],[f1568,f50])).
% 2.48/0.68  fof(f50,plain,(
% 2.48/0.68    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.48/0.68    inference(cnf_transformation,[],[f21])).
% 2.48/0.68  % SZS output end Proof for theBenchmark
% 2.48/0.68  % (27478)------------------------------
% 2.48/0.68  % (27478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.48/0.68  % (27478)Termination reason: Refutation
% 2.48/0.68  
% 2.48/0.68  % (27478)Memory used [KB]: 7036
% 2.48/0.68  % (27478)Time elapsed: 0.203 s
% 2.48/0.68  % (27478)------------------------------
% 2.48/0.68  % (27478)------------------------------
% 2.48/0.68  % (27472)Success in time 0.33 s
%------------------------------------------------------------------------------

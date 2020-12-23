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
% DateTime   : Thu Dec  3 13:19:18 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  260 (19460 expanded)
%              Number of leaves         :   18 (3446 expanded)
%              Depth                    :   38
%              Number of atoms          : 1536 (156516 expanded)
%              Number of equality atoms :  100 (11474 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2425,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2424,f2423])).

fof(f2423,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f2032,f2422])).

fof(f2422,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(global_subsumption,[],[f321,f2169,f2421])).

fof(f2421,plain,
    ( sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f2163,f2420])).

fof(f2420,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2417,f2031])).

fof(f2031,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1997,f53])).

fof(f53,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f1997,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f907,f1993])).

fof(f1993,plain,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f1964,f1992])).

fof(f1992,plain,(
    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1991,f1927])).

fof(f1927,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f1879,f1902])).

fof(f1902,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1901,f482])).

fof(f482,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f295,f192])).

fof(f192,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f117,f76])).

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

fof(f117,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f95,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f55,f75])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f55,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f295,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f294,f104])).

fof(f104,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f103,f56])).

% (10874)Refutation not found, incomplete strategy% (10874)------------------------------
% (10874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10874)Termination reason: Refutation not found, incomplete strategy

% (10874)Memory used [KB]: 6140
% (10874)Time elapsed: 0.372 s
% (10874)------------------------------
% (10874)------------------------------
fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f102,f58])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f89,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f55,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f294,plain,(
    ! [X7] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f293,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f293,plain,(
    ! [X7] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f292,f98])).

fof(f98,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f97,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f96,f58])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f57])).

fof(f87,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,(
    ! [X7] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f291,f58])).

fof(f291,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f290,f57])).

fof(f290,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f289,f56])).

fof(f289,plain,(
    ! [X7] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f288,f117])).

fof(f288,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f251,f116])).

fof(f116,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f115,f57])).

fof(f115,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f94,f58])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(resolution,[],[f55,f74])).

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

fof(f251,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(resolution,[],[f101,f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f101,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f100,f56])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f99,f58])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f88,f57])).

fof(f88,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f55,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1901,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f733,f192])).

fof(f733,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f732,f56])).

fof(f732,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f731,f57])).

fof(f731,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f729,f58])).

fof(f729,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f316,f55])).

fof(f316,plain,(
    ! [X14,X15] :
      ( ~ m1_pre_topc(sK1,X14)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f315,f73])).

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

fof(f315,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f314,f104])).

fof(f314,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f313,f98])).

fof(f313,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f312,f58])).

fof(f312,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f311,f57])).

fof(f311,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f255,f56])).

fof(f255,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(resolution,[],[f101,f81])).

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

fof(f1879,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f593,f55])).

fof(f593,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f592,f56])).

fof(f592,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f591,f57])).

fof(f591,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f589,f58])).

fof(f589,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f310,f55])).

fof(f310,plain,(
    ! [X12,X13] :
      ( ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f309,f104])).

fof(f309,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f308,f98])).

fof(f308,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f307,f58])).

fof(f307,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f306,f57])).

fof(f306,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f254,f56])).

fof(f254,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
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
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f1991,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1990,f1964])).

fof(f1990,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1967,f1906])).

fof(f1906,plain,(
    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f1062,f1902])).

fof(f1062,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f550,f55])).

fof(f550,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f549,f56])).

fof(f549,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f548,f57])).

fof(f548,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f546,f58])).

fof(f546,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f305,f55])).

fof(f305,plain,(
    ! [X10,X11] :
      ( ~ m1_pre_topc(sK1,X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f304,f104])).

fof(f304,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f303,f98])).

fof(f303,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f302,f58])).

fof(f302,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f301,f57])).

fof(f301,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f253,f56])).

fof(f253,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f101,f79])).

fof(f79,plain,(
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
      | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1967,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1033,f1964])).

fof(f1033,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1032,f98])).

fof(f1032,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1031,f519])).

fof(f519,plain,(
    v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f490,f192])).

fof(f490,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f489,f54])).

fof(f489,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f488,f116])).

fof(f488,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f484,f117])).

fof(f484,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f300,f192])).

fof(f300,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X8)
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f299,f104])).

fof(f299,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f298,f98])).

fof(f298,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f297,f58])).

fof(f297,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f296,f57])).

fof(f296,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f252,f56])).

fof(f252,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f101,f78])).

fof(f78,plain,(
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
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1031,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1030,f104])).

fof(f1030,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1029,f101])).

fof(f1029,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f545,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f545,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f544,f54])).

fof(f544,plain,
    ( v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f543,f116])).

fof(f543,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f539,f117])).

fof(f539,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f287,f192])).

fof(f287,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f286,f104])).

fof(f286,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f285,f98])).

fof(f285,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f284,f54])).

fof(f284,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f283,f58])).

fof(f283,plain,(
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
    inference(subsumption_resolution,[],[f282,f57])).

fof(f282,plain,(
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
    inference(subsumption_resolution,[],[f250,f56])).

fof(f250,plain,(
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
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f1964,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1963,f482])).

fof(f1963,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f736,f192])).

fof(f736,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f735,f54])).

fof(f735,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f734,f116])).

fof(f734,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f730,f117])).

fof(f730,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f316,f192])).

fof(f907,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f906,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f906,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f905,f54])).

fof(f905,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f904,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f904,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f898,f192])).

fof(f898,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f273,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f273,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f272,f104])).

fof(f272,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f271,f56])).

fof(f271,plain,(
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
    inference(subsumption_resolution,[],[f270,f98])).

fof(f270,plain,(
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
    inference(subsumption_resolution,[],[f269,f117])).

fof(f269,plain,(
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
    inference(subsumption_resolution,[],[f268,f116])).

fof(f268,plain,(
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
    inference(subsumption_resolution,[],[f267,f54])).

fof(f267,plain,(
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
    inference(subsumption_resolution,[],[f266,f58])).

fof(f266,plain,(
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
    inference(subsumption_resolution,[],[f248,f57])).

fof(f248,plain,(
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
    inference(resolution,[],[f101,f62])).

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
      | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f2417,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2166,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f107,f56])).

fof(f107,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f106,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f58])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f90,f57])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f55,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f2166,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2030,f111])).

fof(f111,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f109,f54])).

fof(f109,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f58])).

fof(f91,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f55,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f2030,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1995,f53])).

fof(f1995,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f880,f1993])).

fof(f880,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f879,f52])).

fof(f879,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f878,f54])).

fof(f878,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f877,f50])).

fof(f877,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f871,f192])).

fof(f871,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f265,f51])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f264,f104])).

fof(f264,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f263,f56])).

fof(f263,plain,(
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
    inference(subsumption_resolution,[],[f262,f98])).

fof(f262,plain,(
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
    inference(subsumption_resolution,[],[f261,f117])).

fof(f261,plain,(
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
    inference(subsumption_resolution,[],[f260,f116])).

fof(f260,plain,(
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
    inference(subsumption_resolution,[],[f259,f54])).

fof(f259,plain,(
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
    inference(subsumption_resolution,[],[f258,f58])).

fof(f258,plain,(
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
    inference(subsumption_resolution,[],[f247,f57])).

fof(f247,plain,(
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
    inference(resolution,[],[f101,f61])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f2163,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2030,f318])).

fof(f318,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f317,f104])).

fof(f317,plain,(
    ! [X16] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f256,f98])).

fof(f256,plain,(
    ! [X16] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(resolution,[],[f101,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f2169,plain,(
    ~ sP4(u1_struct_0(sK1)) ),
    inference(resolution,[],[f2031,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f70,f83_D])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f83_D])).

fof(f83_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f321,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | sP4(u1_struct_0(sK1)) ),
    inference(resolution,[],[f241,f83])).

fof(f241,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f223,f117])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f192,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f2032,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1999,f53])).

fof(f1999,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1043,f1993])).

fof(f1043,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1042,f52])).

fof(f1042,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1041,f54])).

fof(f1041,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1040,f50])).

fof(f1040,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1034,f192])).

fof(f1034,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f281,f51])).

fof(f281,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f280,f104])).

fof(f280,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f279,f56])).

fof(f279,plain,(
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
    inference(subsumption_resolution,[],[f278,f98])).

fof(f278,plain,(
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
    inference(subsumption_resolution,[],[f277,f117])).

fof(f277,plain,(
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
    inference(subsumption_resolution,[],[f276,f116])).

fof(f276,plain,(
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
    inference(subsumption_resolution,[],[f275,f54])).

fof(f275,plain,(
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
    inference(subsumption_resolution,[],[f274,f58])).

fof(f274,plain,(
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
    inference(subsumption_resolution,[],[f249,f57])).

fof(f249,plain,(
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
    inference(resolution,[],[f101,f63])).

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
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2424,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2418,f2031])).

fof(f2418,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2166,f49])).

fof(f49,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:17:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (10870)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (10887)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (10879)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.57  % (10868)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.57  % (10865)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.67/0.58  % (10866)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.67/0.58  % (10869)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.67/0.58  % (10873)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.67/0.58  % (10880)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.67/0.58  % (10867)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.67/0.59  % (10871)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.67/0.59  % (10888)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.67/0.59  % (10882)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.81/0.59  % (10886)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.81/0.59  % (10875)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.81/0.59  % (10885)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.81/0.59  % (10878)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.81/0.60  % (10877)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.81/0.60  % (10884)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.81/0.60  % (10890)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.81/0.60  % (10876)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.81/0.60  % (10864)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.81/0.60  % (10883)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.81/0.61  % (10881)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.81/0.61  % (10874)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.81/0.62  % (10889)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.81/0.62  % (10864)Refutation not found, incomplete strategy% (10864)------------------------------
% 1.81/0.62  % (10864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (10864)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.62  
% 1.81/0.62  % (10864)Memory used [KB]: 10618
% 1.81/0.62  % (10864)Time elapsed: 0.165 s
% 1.81/0.62  % (10864)------------------------------
% 1.81/0.62  % (10864)------------------------------
% 3.06/0.81  % (10869)Refutation found. Thanks to Tanya!
% 3.06/0.81  % SZS status Theorem for theBenchmark
% 3.06/0.83  % SZS output start Proof for theBenchmark
% 3.06/0.83  fof(f2425,plain,(
% 3.06/0.83    $false),
% 3.06/0.83    inference(subsumption_resolution,[],[f2424,f2423])).
% 3.06/0.83  fof(f2423,plain,(
% 3.06/0.83    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.83    inference(backward_demodulation,[],[f2032,f2422])).
% 3.06/0.83  fof(f2422,plain,(
% 3.06/0.83    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.83    inference(global_subsumption,[],[f321,f2169,f2421])).
% 3.06/0.83  fof(f2421,plain,(
% 3.06/0.83    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 3.06/0.83    inference(backward_demodulation,[],[f2163,f2420])).
% 3.06/0.83  fof(f2420,plain,(
% 3.06/0.83    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.83    inference(subsumption_resolution,[],[f2417,f2031])).
% 3.06/0.83  fof(f2031,plain,(
% 3.06/0.83    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1997,f53])).
% 3.06/0.83  fof(f53,plain,(
% 3.06/0.83    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f20,plain,(
% 3.06/0.83    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f19])).
% 3.06/0.83  fof(f19,plain,(
% 3.06/0.83    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f18])).
% 3.06/0.83  fof(f18,negated_conjecture,(
% 3.06/0.83    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.06/0.83    inference(negated_conjecture,[],[f17])).
% 3.06/0.83  fof(f17,conjecture,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 3.06/0.83  fof(f1997,plain,(
% 3.06/0.83    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 3.06/0.83    inference(backward_demodulation,[],[f907,f1993])).
% 3.06/0.83  fof(f1993,plain,(
% 3.06/0.83    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 3.06/0.83    inference(backward_demodulation,[],[f1964,f1992])).
% 3.06/0.83  fof(f1992,plain,(
% 3.06/0.83    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1991,f1927])).
% 3.06/0.83  fof(f1927,plain,(
% 3.06/0.83    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(backward_demodulation,[],[f1879,f1902])).
% 3.06/0.83  fof(f1902,plain,(
% 3.06/0.83    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(forward_demodulation,[],[f1901,f482])).
% 3.06/0.83  fof(f482,plain,(
% 3.06/0.83    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1))),
% 3.06/0.83    inference(resolution,[],[f295,f192])).
% 3.06/0.83  fof(f192,plain,(
% 3.06/0.83    m1_pre_topc(sK1,sK1)),
% 3.06/0.83    inference(resolution,[],[f117,f76])).
% 3.06/0.83  fof(f76,plain,(
% 3.06/0.83    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 3.06/0.83    inference(cnf_transformation,[],[f42])).
% 3.06/0.83  fof(f42,plain,(
% 3.06/0.83    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.06/0.83    inference(ennf_transformation,[],[f12])).
% 3.06/0.83  fof(f12,axiom,(
% 3.06/0.83    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 3.06/0.83  fof(f117,plain,(
% 3.06/0.83    l1_pre_topc(sK1)),
% 3.06/0.83    inference(subsumption_resolution,[],[f95,f58])).
% 3.06/0.83  fof(f58,plain,(
% 3.06/0.83    l1_pre_topc(sK0)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f95,plain,(
% 3.06/0.83    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 3.06/0.83    inference(resolution,[],[f55,f75])).
% 3.06/0.83  fof(f75,plain,(
% 3.06/0.83    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 3.06/0.83    inference(cnf_transformation,[],[f41])).
% 3.06/0.83  fof(f41,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.06/0.83    inference(ennf_transformation,[],[f5])).
% 3.06/0.83  fof(f5,axiom,(
% 3.06/0.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 3.06/0.83  fof(f55,plain,(
% 3.06/0.83    m1_pre_topc(sK1,sK0)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f295,plain,(
% 3.06/0.83    ( ! [X7] : (~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f294,f104])).
% 3.06/0.83  fof(f104,plain,(
% 3.06/0.83    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(subsumption_resolution,[],[f103,f56])).
% 3.06/0.83  % (10874)Refutation not found, incomplete strategy% (10874)------------------------------
% 3.06/0.83  % (10874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.83  % (10874)Termination reason: Refutation not found, incomplete strategy
% 3.06/0.83  
% 3.06/0.83  % (10874)Memory used [KB]: 6140
% 3.06/0.83  % (10874)Time elapsed: 0.372 s
% 3.06/0.83  % (10874)------------------------------
% 3.06/0.83  % (10874)------------------------------
% 3.06/0.83  fof(f56,plain,(
% 3.06/0.83    ~v2_struct_0(sK0)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f103,plain,(
% 3.06/0.83    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(subsumption_resolution,[],[f102,f58])).
% 3.06/0.83  fof(f102,plain,(
% 3.06/0.83    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(subsumption_resolution,[],[f89,f57])).
% 3.06/0.83  fof(f57,plain,(
% 3.06/0.83    v2_pre_topc(sK0)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f89,plain,(
% 3.06/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(resolution,[],[f55,f67])).
% 3.06/0.83  fof(f67,plain,(
% 3.06/0.83    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f28])).
% 3.06/0.83  fof(f28,plain,(
% 3.06/0.83    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f27])).
% 3.06/0.83  fof(f27,plain,(
% 3.06/0.83    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f10])).
% 3.06/0.83  fof(f10,axiom,(
% 3.06/0.83    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 3.06/0.83  fof(f294,plain,(
% 3.06/0.83    ( ! [X7] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f293,f54])).
% 3.06/0.83  fof(f54,plain,(
% 3.06/0.83    ~v2_struct_0(sK1)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f293,plain,(
% 3.06/0.83    ( ! [X7] : (v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f292,f98])).
% 3.06/0.83  fof(f98,plain,(
% 3.06/0.83    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f97,f56])).
% 3.06/0.83  fof(f97,plain,(
% 3.06/0.83    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f96,f58])).
% 3.06/0.83  fof(f96,plain,(
% 3.06/0.83    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f87,f57])).
% 3.06/0.83  fof(f87,plain,(
% 3.06/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(resolution,[],[f55,f65])).
% 3.06/0.83  fof(f65,plain,(
% 3.06/0.83    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f28])).
% 3.06/0.83  fof(f292,plain,(
% 3.06/0.83    ( ! [X7] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f291,f58])).
% 3.06/0.83  fof(f291,plain,(
% 3.06/0.83    ( ! [X7] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f290,f57])).
% 3.06/0.83  fof(f290,plain,(
% 3.06/0.83    ( ! [X7] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f289,f56])).
% 3.06/0.83  fof(f289,plain,(
% 3.06/0.83    ( ! [X7] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f288,f117])).
% 3.06/0.83  fof(f288,plain,(
% 3.06/0.83    ( ! [X7] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f251,f116])).
% 3.06/0.83  fof(f116,plain,(
% 3.06/0.83    v2_pre_topc(sK1)),
% 3.06/0.83    inference(subsumption_resolution,[],[f115,f57])).
% 3.06/0.83  fof(f115,plain,(
% 3.06/0.83    ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 3.06/0.83    inference(subsumption_resolution,[],[f94,f58])).
% 3.06/0.83  fof(f94,plain,(
% 3.06/0.83    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 3.06/0.83    inference(resolution,[],[f55,f74])).
% 3.06/0.83  fof(f74,plain,(
% 3.06/0.83    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 3.06/0.83    inference(cnf_transformation,[],[f40])).
% 3.06/0.83  fof(f40,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.06/0.83    inference(flattening,[],[f39])).
% 3.06/0.83  fof(f39,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f4])).
% 3.06/0.83  fof(f4,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 3.06/0.83  fof(f251,plain,(
% 3.06/0.83    ( ! [X7] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 3.06/0.83    inference(resolution,[],[f101,f77])).
% 3.06/0.83  fof(f77,plain,(
% 3.06/0.83    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f44])).
% 3.06/0.83  fof(f44,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f43])).
% 3.06/0.83  fof(f43,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f7])).
% 3.06/0.83  fof(f7,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 3.06/0.83  fof(f101,plain,(
% 3.06/0.83    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(subsumption_resolution,[],[f100,f56])).
% 3.06/0.83  fof(f100,plain,(
% 3.06/0.83    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(subsumption_resolution,[],[f99,f58])).
% 3.06/0.83  fof(f99,plain,(
% 3.06/0.83    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(subsumption_resolution,[],[f88,f57])).
% 3.06/0.83  fof(f88,plain,(
% 3.06/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(resolution,[],[f55,f66])).
% 3.06/0.83  fof(f66,plain,(
% 3.06/0.83    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f28])).
% 3.06/0.83  fof(f1901,plain,(
% 3.06/0.83    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(resolution,[],[f733,f192])).
% 3.06/0.83  fof(f733,plain,(
% 3.06/0.83    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f732,f56])).
% 3.06/0.83  fof(f732,plain,(
% 3.06/0.83    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f731,f57])).
% 3.06/0.83  fof(f731,plain,(
% 3.06/0.83    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f729,f58])).
% 3.06/0.83  fof(f729,plain,(
% 3.06/0.83    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(resolution,[],[f316,f55])).
% 3.06/0.83  fof(f316,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~m1_pre_topc(sK1,X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | v2_struct_0(X14) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f315,f73])).
% 3.06/0.83  fof(f73,plain,(
% 3.06/0.83    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 3.06/0.83    inference(cnf_transformation,[],[f38])).
% 3.06/0.83  fof(f38,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.06/0.83    inference(flattening,[],[f37])).
% 3.06/0.83  fof(f37,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f15])).
% 3.06/0.83  fof(f15,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 3.06/0.83  fof(f315,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f314,f104])).
% 3.06/0.83  fof(f314,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f313,f98])).
% 3.06/0.83  fof(f313,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f312,f58])).
% 3.06/0.83  fof(f312,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f311,f57])).
% 3.06/0.83  fof(f311,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f255,f56])).
% 3.06/0.83  fof(f255,plain,(
% 3.06/0.83    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 3.06/0.83    inference(resolution,[],[f101,f81])).
% 3.06/0.83  fof(f81,plain,(
% 3.06/0.83    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f48])).
% 3.06/0.83  fof(f48,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f47])).
% 3.06/0.83  fof(f47,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f8])).
% 3.06/0.83  fof(f8,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 3.06/0.83  fof(f1879,plain,(
% 3.06/0.83    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(resolution,[],[f593,f55])).
% 3.06/0.83  fof(f593,plain,(
% 3.06/0.83    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f592,f56])).
% 3.06/0.83  fof(f592,plain,(
% 3.06/0.83    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f591,f57])).
% 3.06/0.83  fof(f591,plain,(
% 3.06/0.83    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f589,f58])).
% 3.06/0.83  fof(f589,plain,(
% 3.06/0.83    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(resolution,[],[f310,f55])).
% 3.06/0.83  fof(f310,plain,(
% 3.06/0.83    ( ! [X12,X13] : (~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f309,f104])).
% 3.06/0.83  fof(f309,plain,(
% 3.06/0.83    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f308,f98])).
% 3.06/0.83  fof(f308,plain,(
% 3.06/0.83    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f307,f58])).
% 3.06/0.83  fof(f307,plain,(
% 3.06/0.83    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f306,f57])).
% 3.06/0.83  fof(f306,plain,(
% 3.06/0.83    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f254,f56])).
% 3.06/0.83  fof(f254,plain,(
% 3.06/0.83    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 3.06/0.83    inference(resolution,[],[f101,f80])).
% 3.06/0.83  fof(f80,plain,(
% 3.06/0.83    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f46])).
% 3.06/0.83  fof(f46,plain,(
% 3.06/0.83    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f45])).
% 3.06/0.83  fof(f45,plain,(
% 3.06/0.83    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f9])).
% 3.06/0.83  fof(f9,axiom,(
% 3.06/0.83    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 3.06/0.83  fof(f1991,plain,(
% 3.06/0.83    ~m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(forward_demodulation,[],[f1990,f1964])).
% 3.06/0.83  fof(f1990,plain,(
% 3.06/0.83    ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1967,f1906])).
% 3.06/0.83  fof(f1906,plain,(
% 3.06/0.83    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(backward_demodulation,[],[f1062,f1902])).
% 3.06/0.83  fof(f1062,plain,(
% 3.06/0.83    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(resolution,[],[f550,f55])).
% 3.06/0.83  fof(f550,plain,(
% 3.06/0.83    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f549,f56])).
% 3.06/0.83  fof(f549,plain,(
% 3.06/0.83    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f548,f57])).
% 3.06/0.83  fof(f548,plain,(
% 3.06/0.83    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f546,f58])).
% 3.06/0.83  fof(f546,plain,(
% 3.06/0.83    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(resolution,[],[f305,f55])).
% 3.06/0.83  fof(f305,plain,(
% 3.06/0.83    ( ! [X10,X11] : (~m1_pre_topc(sK1,X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f304,f104])).
% 3.06/0.83  fof(f304,plain,(
% 3.06/0.83    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f303,f98])).
% 3.06/0.83  fof(f303,plain,(
% 3.06/0.83    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f302,f58])).
% 3.06/0.83  fof(f302,plain,(
% 3.06/0.83    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f301,f57])).
% 3.06/0.83  fof(f301,plain,(
% 3.06/0.83    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f253,f56])).
% 3.06/0.83  fof(f253,plain,(
% 3.06/0.83    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 3.06/0.83    inference(resolution,[],[f101,f79])).
% 3.06/0.83  fof(f79,plain,(
% 3.06/0.83    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f46])).
% 3.06/0.83  fof(f1967,plain,(
% 3.06/0.83    ~v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(backward_demodulation,[],[f1033,f1964])).
% 3.06/0.83  fof(f1033,plain,(
% 3.06/0.83    ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1032,f98])).
% 3.06/0.83  fof(f1032,plain,(
% 3.06/0.83    ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1031,f519])).
% 3.06/0.83  fof(f519,plain,(
% 3.06/0.83    v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 3.06/0.83    inference(resolution,[],[f490,f192])).
% 3.06/0.83  fof(f490,plain,(
% 3.06/0.83    ( ! [X1] : (~m1_pre_topc(X1,sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f489,f54])).
% 3.06/0.83  fof(f489,plain,(
% 3.06/0.83    ( ! [X1] : (~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f488,f116])).
% 3.06/0.83  fof(f488,plain,(
% 3.06/0.83    ( ! [X1] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f484,f117])).
% 3.06/0.83  fof(f484,plain,(
% 3.06/0.83    ( ! [X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(resolution,[],[f300,f192])).
% 3.06/0.83  fof(f300,plain,(
% 3.06/0.83    ( ! [X8,X9] : (~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X8) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f299,f104])).
% 3.06/0.83  fof(f299,plain,(
% 3.06/0.83    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f298,f98])).
% 3.06/0.83  fof(f298,plain,(
% 3.06/0.83    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f297,f58])).
% 3.06/0.83  fof(f297,plain,(
% 3.06/0.83    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f296,f57])).
% 3.06/0.83  fof(f296,plain,(
% 3.06/0.83    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f252,f56])).
% 3.06/0.83  fof(f252,plain,(
% 3.06/0.83    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(resolution,[],[f101,f78])).
% 3.06/0.83  fof(f78,plain,(
% 3.06/0.83    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f46])).
% 3.06/0.83  fof(f1031,plain,(
% 3.06/0.83    ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1030,f104])).
% 3.06/0.83  fof(f1030,plain,(
% 3.06/0.83    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1029,f101])).
% 3.06/0.83  fof(f1029,plain,(
% 3.06/0.83    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(resolution,[],[f545,f60])).
% 3.06/0.83  fof(f60,plain,(
% 3.06/0.83    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~v1_funct_1(X2)) )),
% 3.06/0.83    inference(cnf_transformation,[],[f22])).
% 3.06/0.83  fof(f22,plain,(
% 3.06/0.83    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.06/0.83    inference(flattening,[],[f21])).
% 3.06/0.83  fof(f21,plain,(
% 3.06/0.83    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.06/0.83    inference(ennf_transformation,[],[f3])).
% 3.06/0.83  fof(f3,axiom,(
% 3.06/0.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 3.06/0.83  fof(f545,plain,(
% 3.06/0.83    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 3.06/0.83    inference(subsumption_resolution,[],[f544,f54])).
% 3.06/0.83  fof(f544,plain,(
% 3.06/0.83    v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 3.06/0.83    inference(subsumption_resolution,[],[f543,f116])).
% 3.06/0.83  fof(f543,plain,(
% 3.06/0.83    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 3.06/0.83    inference(subsumption_resolution,[],[f539,f117])).
% 3.06/0.83  fof(f539,plain,(
% 3.06/0.83    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 3.06/0.83    inference(resolution,[],[f287,f192])).
% 3.06/0.83  fof(f287,plain,(
% 3.06/0.83    ( ! [X6] : (~m1_pre_topc(sK1,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f286,f104])).
% 3.06/0.83  fof(f286,plain,(
% 3.06/0.83    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f285,f98])).
% 3.06/0.83  fof(f285,plain,(
% 3.06/0.83    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f284,f54])).
% 3.06/0.83  fof(f284,plain,(
% 3.06/0.83    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f283,f58])).
% 3.06/0.83  fof(f283,plain,(
% 3.06/0.83    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f282,f57])).
% 3.06/0.83  fof(f282,plain,(
% 3.06/0.83    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f250,f56])).
% 3.06/0.83  fof(f250,plain,(
% 3.06/0.83    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 3.06/0.83    inference(resolution,[],[f101,f64])).
% 3.06/0.83  fof(f64,plain,(
% 3.06/0.83    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f26])).
% 3.06/0.83  fof(f26,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f25])).
% 3.06/0.83  fof(f25,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f14])).
% 3.06/0.83  fof(f14,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 3.06/0.83  fof(f1964,plain,(
% 3.06/0.83    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(forward_demodulation,[],[f1963,f482])).
% 3.06/0.83  fof(f1963,plain,(
% 3.06/0.83    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 3.06/0.83    inference(resolution,[],[f736,f192])).
% 3.06/0.83  fof(f736,plain,(
% 3.06/0.83    ( ! [X1] : (~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f735,f54])).
% 3.06/0.83  fof(f735,plain,(
% 3.06/0.83    ( ! [X1] : (v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f734,f116])).
% 3.06/0.83  fof(f734,plain,(
% 3.06/0.83    ( ! [X1] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f730,f117])).
% 3.06/0.83  fof(f730,plain,(
% 3.06/0.83    ( ! [X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 3.06/0.83    inference(resolution,[],[f316,f192])).
% 3.06/0.83  fof(f907,plain,(
% 3.06/0.83    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.83    inference(subsumption_resolution,[],[f906,f52])).
% 3.06/0.83  fof(f52,plain,(
% 3.06/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f906,plain,(
% 3.06/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.83    inference(subsumption_resolution,[],[f905,f54])).
% 3.06/0.83  fof(f905,plain,(
% 3.06/0.83    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.83    inference(subsumption_resolution,[],[f904,f50])).
% 3.06/0.83  fof(f50,plain,(
% 3.06/0.83    v1_funct_1(sK2)),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f904,plain,(
% 3.06/0.83    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.83    inference(subsumption_resolution,[],[f898,f192])).
% 3.06/0.83  fof(f898,plain,(
% 3.06/0.83    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.83    inference(resolution,[],[f273,f51])).
% 3.06/0.83  fof(f51,plain,(
% 3.06/0.83    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.06/0.83    inference(cnf_transformation,[],[f20])).
% 3.06/0.83  fof(f273,plain,(
% 3.06/0.83    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | v2_struct_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f272,f104])).
% 3.06/0.83  fof(f272,plain,(
% 3.06/0.83    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f271,f56])).
% 3.06/0.83  fof(f271,plain,(
% 3.06/0.83    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f270,f98])).
% 3.06/0.83  fof(f270,plain,(
% 3.06/0.83    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f269,f117])).
% 3.06/0.83  fof(f269,plain,(
% 3.06/0.83    ( ! [X2,X3] : (~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f268,f116])).
% 3.06/0.83  fof(f268,plain,(
% 3.06/0.83    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f267,f54])).
% 3.06/0.83  fof(f267,plain,(
% 3.06/0.83    ( ! [X2,X3] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f266,f58])).
% 3.06/0.83  fof(f266,plain,(
% 3.06/0.83    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f248,f57])).
% 3.06/0.83  fof(f248,plain,(
% 3.06/0.83    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 3.06/0.83    inference(resolution,[],[f101,f62])).
% 3.06/0.83  fof(f62,plain,(
% 3.06/0.83    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 3.06/0.83    inference(cnf_transformation,[],[f24])).
% 3.06/0.83  fof(f24,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f23])).
% 3.06/0.83  fof(f23,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f13])).
% 3.06/0.83  fof(f13,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 3.06/0.83  fof(f2417,plain,(
% 3.06/0.83    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.83    inference(resolution,[],[f2166,f108])).
% 3.06/0.83  fof(f108,plain,(
% 3.06/0.83    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f107,f56])).
% 3.06/0.83  fof(f107,plain,(
% 3.06/0.83    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f106,f54])).
% 3.06/0.83  fof(f106,plain,(
% 3.06/0.83    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f105,f58])).
% 3.06/0.83  fof(f105,plain,(
% 3.06/0.83    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f90,f57])).
% 3.06/0.83  fof(f90,plain,(
% 3.06/0.83    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 3.06/0.83    inference(resolution,[],[f55,f68])).
% 3.06/0.83  fof(f68,plain,(
% 3.06/0.83    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 3.06/0.83    inference(cnf_transformation,[],[f30])).
% 3.06/0.83  fof(f30,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f29])).
% 3.06/0.83  fof(f29,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f16])).
% 3.06/0.83  fof(f16,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 3.06/0.83  fof(f2166,plain,(
% 3.06/0.83    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))),
% 3.06/0.83    inference(resolution,[],[f2030,f111])).
% 3.06/0.83  fof(f111,plain,(
% 3.06/0.83    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f110,f56])).
% 3.06/0.83  fof(f110,plain,(
% 3.06/0.83    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f109,f54])).
% 3.06/0.83  fof(f109,plain,(
% 3.06/0.83    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 3.06/0.83    inference(subsumption_resolution,[],[f91,f58])).
% 3.06/0.83  fof(f91,plain,(
% 3.06/0.83    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 3.06/0.83    inference(resolution,[],[f55,f71])).
% 3.06/0.83  fof(f71,plain,(
% 3.06/0.83    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 3.06/0.83    inference(cnf_transformation,[],[f35])).
% 3.06/0.83  fof(f35,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.06/0.83    inference(flattening,[],[f34])).
% 3.06/0.83  fof(f34,plain,(
% 3.06/0.83    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.06/0.83    inference(ennf_transformation,[],[f6])).
% 3.06/0.83  fof(f6,axiom,(
% 3.06/0.83    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.06/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 3.06/0.83  fof(f2030,plain,(
% 3.06/0.83    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 3.06/0.83    inference(subsumption_resolution,[],[f1995,f53])).
% 3.06/0.83  fof(f1995,plain,(
% 3.06/0.83    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 3.06/0.83    inference(backward_demodulation,[],[f880,f1993])).
% 3.06/0.84  fof(f880,plain,(
% 3.06/0.84    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f879,f52])).
% 3.06/0.84  fof(f879,plain,(
% 3.06/0.84    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f878,f54])).
% 3.06/0.84  fof(f878,plain,(
% 3.06/0.84    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f877,f50])).
% 3.06/0.84  fof(f877,plain,(
% 3.06/0.84    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f871,f192])).
% 3.06/0.84  fof(f871,plain,(
% 3.06/0.84    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(resolution,[],[f265,f51])).
% 3.06/0.84  fof(f265,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(X1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f264,f104])).
% 3.06/0.84  fof(f264,plain,(
% 3.06/0.84    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f263,f56])).
% 3.06/0.84  fof(f263,plain,(
% 3.06/0.84    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f262,f98])).
% 3.06/0.84  fof(f262,plain,(
% 3.06/0.84    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f261,f117])).
% 3.06/0.84  fof(f261,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f260,f116])).
% 3.06/0.84  fof(f260,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f259,f54])).
% 3.06/0.84  fof(f259,plain,(
% 3.06/0.84    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f258,f58])).
% 3.06/0.84  fof(f258,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f247,f57])).
% 3.06/0.84  fof(f247,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 3.06/0.84    inference(resolution,[],[f101,f61])).
% 3.06/0.84  fof(f61,plain,(
% 3.06/0.84    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 3.06/0.84    inference(cnf_transformation,[],[f24])).
% 3.06/0.84  fof(f2163,plain,(
% 3.06/0.84    v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.84    inference(resolution,[],[f2030,f318])).
% 3.06/0.84  fof(f318,plain,(
% 3.06/0.84    ( ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f317,f104])).
% 3.06/0.84  fof(f317,plain,(
% 3.06/0.84    ( ! [X16] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f256,f98])).
% 3.06/0.84  fof(f256,plain,(
% 3.06/0.84    ( ! [X16] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 3.06/0.84    inference(resolution,[],[f101,f69])).
% 3.06/0.84  fof(f69,plain,(
% 3.06/0.84    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 3.06/0.84    inference(cnf_transformation,[],[f32])).
% 3.06/0.84  fof(f32,plain,(
% 3.06/0.84    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.06/0.84    inference(flattening,[],[f31])).
% 3.06/0.84  fof(f31,plain,(
% 3.06/0.84    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.06/0.84    inference(ennf_transformation,[],[f2])).
% 3.06/0.84  fof(f2,axiom,(
% 3.06/0.84    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.06/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 3.06/0.84  fof(f2169,plain,(
% 3.06/0.84    ~sP4(u1_struct_0(sK1))),
% 3.06/0.84    inference(resolution,[],[f2031,f84])).
% 3.06/0.84  fof(f84,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP4(X1)) )),
% 3.06/0.84    inference(general_splitting,[],[f70,f83_D])).
% 3.06/0.84  fof(f83,plain,(
% 3.06/0.84    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP4(X1)) )),
% 3.06/0.84    inference(cnf_transformation,[],[f83_D])).
% 3.06/0.84  fof(f83_D,plain,(
% 3.06/0.84    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP4(X1)) )),
% 3.06/0.84    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 3.06/0.84  fof(f70,plain,(
% 3.06/0.84    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 3.06/0.84    inference(cnf_transformation,[],[f33])).
% 3.06/0.84  fof(f33,plain,(
% 3.06/0.84    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.06/0.84    inference(ennf_transformation,[],[f1])).
% 3.06/0.84  fof(f1,axiom,(
% 3.06/0.84    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.06/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 3.06/0.84  fof(f321,plain,(
% 3.06/0.84    ~v1_xboole_0(u1_struct_0(sK1)) | sP4(u1_struct_0(sK1))),
% 3.06/0.84    inference(resolution,[],[f241,f83])).
% 3.06/0.84  fof(f241,plain,(
% 3.06/0.84    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.06/0.84    inference(subsumption_resolution,[],[f223,f117])).
% 3.06/0.84  fof(f223,plain,(
% 3.06/0.84    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.06/0.84    inference(resolution,[],[f192,f72])).
% 3.06/0.84  fof(f72,plain,(
% 3.06/0.84    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.06/0.84    inference(cnf_transformation,[],[f36])).
% 3.06/0.84  fof(f36,plain,(
% 3.06/0.84    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.06/0.84    inference(ennf_transformation,[],[f11])).
% 3.06/0.84  fof(f11,axiom,(
% 3.06/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.06/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 3.06/0.84  fof(f2032,plain,(
% 3.06/0.84    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.84    inference(subsumption_resolution,[],[f1999,f53])).
% 3.06/0.84  fof(f1999,plain,(
% 3.06/0.84    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.84    inference(backward_demodulation,[],[f1043,f1993])).
% 3.06/0.84  fof(f1043,plain,(
% 3.06/0.84    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f1042,f52])).
% 3.06/0.84  fof(f1042,plain,(
% 3.06/0.84    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f1041,f54])).
% 3.06/0.84  fof(f1041,plain,(
% 3.06/0.84    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f1040,f50])).
% 3.06/0.84  fof(f1040,plain,(
% 3.06/0.84    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(subsumption_resolution,[],[f1034,f192])).
% 3.06/0.84  fof(f1034,plain,(
% 3.06/0.84    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 3.06/0.84    inference(resolution,[],[f281,f51])).
% 3.06/0.84  fof(f281,plain,(
% 3.06/0.84    ( ! [X4,X5] : (~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(X5) | v2_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f280,f104])).
% 3.06/0.84  fof(f280,plain,(
% 3.06/0.84    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f279,f56])).
% 3.06/0.84  fof(f279,plain,(
% 3.06/0.84    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f278,f98])).
% 3.06/0.84  fof(f278,plain,(
% 3.06/0.84    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f277,f117])).
% 3.06/0.84  fof(f277,plain,(
% 3.06/0.84    ( ! [X4,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f276,f116])).
% 3.06/0.84  fof(f276,plain,(
% 3.06/0.84    ( ! [X4,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f275,f54])).
% 3.06/0.84  fof(f275,plain,(
% 3.06/0.84    ( ! [X4,X5] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f274,f58])).
% 3.06/0.84  fof(f274,plain,(
% 3.06/0.84    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.84    inference(subsumption_resolution,[],[f249,f57])).
% 3.06/0.85  fof(f249,plain,(
% 3.06/0.85    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 3.06/0.85    inference(resolution,[],[f101,f63])).
% 3.06/0.85  fof(f63,plain,(
% 3.06/0.85    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 3.06/0.85    inference(cnf_transformation,[],[f24])).
% 3.06/0.85  fof(f2424,plain,(
% 3.06/0.85    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.85    inference(subsumption_resolution,[],[f2418,f2031])).
% 3.06/0.85  fof(f2418,plain,(
% 3.06/0.85    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 3.06/0.85    inference(resolution,[],[f2166,f49])).
% 3.06/0.85  fof(f49,plain,(
% 3.06/0.85    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 3.06/0.85    inference(cnf_transformation,[],[f20])).
% 3.06/0.85  % SZS output end Proof for theBenchmark
% 3.06/0.85  % (10869)------------------------------
% 3.06/0.85  % (10869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.85  % (10869)Termination reason: Refutation
% 3.06/0.85  
% 3.06/0.85  % (10869)Memory used [KB]: 7803
% 3.06/0.85  % (10869)Time elapsed: 0.384 s
% 3.06/0.85  % (10869)------------------------------
% 3.06/0.85  % (10869)------------------------------
% 3.06/0.85  % (10859)Success in time 0.483 s
%------------------------------------------------------------------------------

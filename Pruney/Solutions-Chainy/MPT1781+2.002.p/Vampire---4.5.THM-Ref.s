%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:16 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  275 (4789 expanded)
%              Number of leaves         :   16 ( 849 expanded)
%              Depth                    :   94
%              Number of atoms          : 1728 (38415 expanded)
%              Number of equality atoms :  218 (3287 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f821,plain,(
    $false ),
    inference(subsumption_resolution,[],[f754,f105])).

fof(f105,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f104,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | r2_funct_2(X0,X1,sK2,sK2) ) ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f754,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(backward_demodulation,[],[f50,f753])).

fof(f753,plain,(
    sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f752,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f752,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f751,f52])).

fof(f52,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

% (31963)Refutation not found, incomplete strategy% (31963)------------------------------
% (31963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31963)Termination reason: Refutation not found, incomplete strategy

% (31963)Memory used [KB]: 1791
% (31963)Time elapsed: 0.128 s
% (31963)------------------------------
% (31963)------------------------------
fof(f751,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f750,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f750,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f749,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f749,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f748,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f748,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f747,f53])).

fof(f747,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f746,f52])).

fof(f746,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f745,f55])).

fof(f745,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f744,f54])).

fof(f744,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f743,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f743,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f742,f47])).

fof(f742,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f741,f49])).

fof(f741,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f740,f48])).

fof(f740,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f739])).

fof(f739,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f738,f270])).

fof(f270,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,sK1))
      | k4_tmap_1(sK0,sK1) = X0
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f267,f52])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
      | k4_tmap_1(sK0,X1) = X0
      | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f266,f53])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
      | k4_tmap_1(sK0,X1) = X0
      | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f264,f54])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
      | k4_tmap_1(sK0,X1) = X0
      | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,X1))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f263,f55])).

fof(f263,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | k4_tmap_1(X2,X1) = X0
      | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k4_tmap_1(X2,X1))
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f262,f75])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(k4_tmap_1(X2,X1),u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | k4_tmap_1(X2,X1) = X0
      | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k4_tmap_1(X2,X1))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(k4_tmap_1(X2,X1),u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | k4_tmap_1(X2,X1) = X0
      | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k4_tmap_1(X2,X1))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f155,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f155,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ m1_subset_1(k4_tmap_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(k4_tmap_1(X6,X7),X4,X5)
      | ~ v1_funct_2(X3,X4,X5)
      | k4_tmap_1(X6,X7) = X3
      | ~ r2_funct_2(X4,X5,X3,k4_tmap_1(X6,X7))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f82,f74])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f738,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f737,f53])).

fof(f737,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f736,f52])).

fof(f736,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f735,f55])).

fof(f735,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f734,f54])).

fof(f734,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f733,f76])).

fof(f733,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f732,f719])).

fof(f719,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f718,f47])).

fof(f718,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f717,f49])).

fof(f717,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f716,f48])).

fof(f716,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f701,f270])).

fof(f701,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f563,f700])).

fof(f700,plain,
    ( r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f699,f49])).

fof(f699,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f698,f47])).

fof(f698,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f697,f48])).

fof(f697,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f695,f387])).

fof(f387,plain,(
    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f386,f55])).

fof(f386,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f385,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f385,plain,
    ( ~ l1_struct_0(sK0)
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f384,f88])).

fof(f88,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f87,f52])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f60,f55])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f384,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f383,f59])).

fof(f383,plain,
    ( ~ l1_struct_0(sK1)
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f381,f53])).

fof(f381,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f380,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f380,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f378,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f378,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f377,f62])).

fof(f377,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f376,f88])).

fof(f376,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f375,f132])).

fof(f132,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f130,f52])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0) ) ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f127,f55])).

fof(f127,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | m1_pre_topc(X7,X7)
      | ~ v2_pre_topc(X6) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(X7,X6)
      | m1_pre_topc(X7,X7)
      | ~ v2_pre_topc(X6) ) ),
    inference(resolution,[],[f71,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

% (31976)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f375,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f374,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f374,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f373])).

fof(f373,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f372,f198])).

fof(f198,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f193,f132])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f192,f47])).

fof(f192,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f190,f48])).

fof(f190,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f185,f49])).

fof(f185,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,sK1)
      | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f184,f51])).

fof(f184,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,sK1)
      | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f181,f93])).

fof(f93,plain,(
    v2_pre_topc(sK1) ),
    inference(resolution,[],[f92,f52])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f90,f54])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f181,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,sK1)
      | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f177,f88])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f176,f54])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f174,f53])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f372,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f371,f49])).

fof(f371,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f370,f48])).

fof(f370,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f369,f47])).

fof(f369,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f368])).

fof(f368,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(superposition,[],[f58,f330])).

fof(f330,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f329,f55])).

fof(f329,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f328,f59])).

fof(f328,plain,
    ( ~ l1_struct_0(sK0)
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f327,f88])).

fof(f327,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f326,f59])).

fof(f326,plain,
    ( ~ l1_struct_0(sK1)
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f324,f53])).

fof(f324,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f323,f62])).

fof(f323,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f321,f51])).

fof(f321,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f315,f62])).

fof(f315,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f314,f198])).

fof(f314,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f313,f48])).

fof(f313,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f311,f47])).

fof(f311,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f303,f49])).

fof(f303,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0))
      | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1))
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f302,f88])).

fof(f302,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0))
      | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f288,f132])).

fof(f288,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0))
      | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK1)
      | ~ l1_pre_topc(sK1)
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0))
      | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK1)
      | ~ l1_pre_topc(sK1)
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) ) ),
    inference(resolution,[],[f260,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | k1_funct_1(sK2,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f152,f48])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k1_funct_1(sK2,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) ) ),
    inference(resolution,[],[f150,f49])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) ) ),
    inference(resolution,[],[f80,f47])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

% (31979)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f260,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(u1_struct_0(X1),u1_struct_0(sK0),X0,u1_struct_0(sK1),sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
      | sK2 = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f259,f61])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
      | ~ v1_funct_2(X0,X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(u1_struct_0(sK0))
      | m1_subset_1(sK3(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1),sK2),X1)
      | sK2 = k2_partfun1(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f258,f48])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | m1_subset_1(sK3(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1),sK2),X1)
      | sK2 = k2_partfun1(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f204,f49])).

fof(f204,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | v1_xboole_0(X2)
      | ~ v1_funct_2(sK2,X3,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(sK3(X2,X0,X1,X3,sK2),X2)
      | sK2 = k2_partfun1(X2,X0,X1,X3) ) ),
    inference(resolution,[],[f56,f47])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK3(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0)
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f695,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f694,f53])).

fof(f694,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f693,f52])).

fof(f693,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f692,f55])).

fof(f692,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f691,f54])).

fof(f691,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f690,f74])).

fof(f690,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f689,f53])).

fof(f689,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f688,f52])).

fof(f688,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f687,f55])).

fof(f687,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f686,f54])).

fof(f686,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f679,f75])).

fof(f679,plain,(
    ! [X1] :
      ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f678,f53])).

fof(f678,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f677,f52])).

fof(f677,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f676,f55])).

fof(f676,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f673,f54])).

fof(f673,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f669,f76])).

fof(f669,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f668,f54])).

fof(f668,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_hidden(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f666,f53])).

fof(f666,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_hidden(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1) ) ),
    inference(resolution,[],[f665,f55])).

fof(f665,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | r2_hidden(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2) ) ),
    inference(subsumption_resolution,[],[f664,f51])).

fof(f664,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | r2_hidden(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2) ) ),
    inference(resolution,[],[f546,f132])).

fof(f546,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X4)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | r2_hidden(sK4(X4,sK1,X5,X6,X7),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7) ) ),
    inference(subsumption_resolution,[],[f545,f93])).

fof(f545,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | r2_hidden(sK4(X4,sK1,X5,X6,X7),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7) ) ),
    inference(subsumption_resolution,[],[f542,f51])).

fof(f542,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | r2_hidden(sK4(X4,sK1,X5,X6,X7),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7) ) ),
    inference(resolution,[],[f64,f88])).

% (31957)Refutation not found, incomplete strategy% (31957)------------------------------
% (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31957)Termination reason: Refutation not found, incomplete strategy

% (31957)Memory used [KB]: 10746
% (31957)Time elapsed: 0.113 s
% (31957)------------------------------
% (31957)------------------------------
fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | r2_hidden(sK4(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

% (31962)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f563,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f561,f46])).

fof(f46,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f561,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f556,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f100,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f98,f52])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f96,f53])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f556,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f555,f49])).

fof(f555,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f554,f47])).

fof(f554,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f553,f48])).

fof(f553,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f551,f387])).

fof(f551,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f550,f53])).

fof(f550,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f549,f52])).

fof(f549,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f548,f55])).

fof(f548,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f547,f54])).

fof(f547,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f540,f74])).

fof(f540,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f539,f53])).

fof(f539,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f538,f52])).

% (31967)Refutation not found, incomplete strategy% (31967)------------------------------
% (31967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31967)Termination reason: Refutation not found, incomplete strategy

% (31967)Memory used [KB]: 10746
% (31967)Time elapsed: 0.134 s
% (31967)------------------------------
% (31967)------------------------------
fof(f538,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f537,f55])).

fof(f537,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f536,f54])).

fof(f536,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f529,f75])).

fof(f529,plain,(
    ! [X1] :
      ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f528,f53])).

fof(f528,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f527,f52])).

fof(f527,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f526,f55])).

fof(f526,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f523,f54])).

fof(f523,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f519,f76])).

fof(f519,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f518,f54])).

fof(f518,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f516,f53])).

fof(f516,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1) ) ),
    inference(resolution,[],[f515,f55])).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | m1_subset_1(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2) ) ),
    inference(subsumption_resolution,[],[f514,f51])).

fof(f514,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | m1_subset_1(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2) ) ),
    inference(resolution,[],[f456,f132])).

fof(f456,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X4)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | m1_subset_1(sK4(X4,sK1,X5,X6,X7),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7) ) ),
    inference(subsumption_resolution,[],[f455,f93])).

fof(f455,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | m1_subset_1(sK4(X4,sK1,X5,X6,X7),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7) ) ),
    inference(subsumption_resolution,[],[f452,f51])).

fof(f452,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | m1_subset_1(sK4(X4,sK1,X5,X6,X7),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7) ) ),
    inference(resolution,[],[f63,f88])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | m1_subset_1(sK4(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f732,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f731])).

fof(f731,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sK2 = k4_tmap_1(sK0,sK1)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f619,f730])).

fof(f730,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f729,f47])).

% (31961)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f729,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f728,f49])).

fof(f728,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f727,f48])).

fof(f727,plain,
    ( sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f713,f270])).

fof(f713,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f712,f51])).

fof(f712,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK1)
    | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f711,f52])).

fof(f711,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f708])).

fof(f708,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f700,f562])).

fof(f562,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
      | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,X0),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f561,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(X0))
      | k1_funct_1(k4_tmap_1(sK0,X0),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f144,f53])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(X0))
      | k1_funct_1(k4_tmap_1(sK0,X0),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f142,f54])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(X0))
      | k1_funct_1(k4_tmap_1(sK0,X0),X1) = X1 ) ),
    inference(resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f619,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f618,f387])).

fof(f618,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f617,f53])).

fof(f617,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f616,f49])).

fof(f616,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f615,f48])).

fof(f615,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f614,f47])).

fof(f614,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f613,f132])).

fof(f613,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f612,f88])).

fof(f612,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f611,f93])).

fof(f611,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f610,f51])).

fof(f610,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f609,f55])).

fof(f609,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f608,f54])).

% (31971)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f608,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f607])).

fof(f607,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f65,f572])).

fof(f572,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f571,f88])).

fof(f571,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f570,f59])).

fof(f570,plain,
    ( ~ l1_struct_0(sK1)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f568,f51])).

fof(f568,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f567,f62])).

fof(f567,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f566,f47])).

fof(f566,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f565,f49])).

fof(f565,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f564,f48])).

fof(f564,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f559,f270])).

fof(f559,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f556,f153])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,sK4(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK4(X0,X1,X2,X3,X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (31965)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (31975)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (31956)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (31956)Refutation not found, incomplete strategy% (31956)------------------------------
% 0.20/0.50  % (31956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31956)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (31956)Memory used [KB]: 10618
% 0.20/0.50  % (31956)Time elapsed: 0.083 s
% 0.20/0.50  % (31956)------------------------------
% 0.20/0.50  % (31956)------------------------------
% 0.20/0.50  % (31978)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (31959)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (31977)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (31967)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (31960)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (31964)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (31957)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (31966)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (31973)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.52  % (31968)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.32/0.52  % (31980)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.53  % (31969)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.32/0.53  % (31970)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.32/0.53  % (31963)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.32/0.53  % (31958)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.32/0.53  % (31981)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.32/0.53  % (31975)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f821,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(subsumption_resolution,[],[f754,f105])).
% 1.32/0.53  fof(f105,plain,(
% 1.32/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 1.32/0.53    inference(subsumption_resolution,[],[f104,f48])).
% 1.32/0.53  fof(f48,plain,(
% 1.32/0.53    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.53    inference(flattening,[],[f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,negated_conjecture,(
% 1.32/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.32/0.53    inference(negated_conjecture,[],[f17])).
% 1.32/0.53  fof(f17,conjecture,(
% 1.32/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 1.32/0.53    inference(resolution,[],[f102,f49])).
% 1.32/0.53  fof(f49,plain,(
% 1.32/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f102,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2)) )),
% 1.32/0.53    inference(resolution,[],[f86,f47])).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    v1_funct_1(sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f86,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f85])).
% 1.32/0.53  fof(f85,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.32/0.53    inference(equality_resolution,[],[f81])).
% 1.32/0.53  fof(f81,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f45])).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.32/0.53    inference(flattening,[],[f44])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.32/0.53    inference(ennf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.32/0.53  fof(f754,plain,(
% 1.32/0.53    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 1.32/0.53    inference(backward_demodulation,[],[f50,f753])).
% 1.32/0.53  fof(f753,plain,(
% 1.32/0.53    sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f752,f53])).
% 1.32/0.53  fof(f53,plain,(
% 1.32/0.53    ~v2_struct_0(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f752,plain,(
% 1.32/0.53    sK2 = k4_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f751,f52])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    m1_pre_topc(sK1,sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  % (31963)Refutation not found, incomplete strategy% (31963)------------------------------
% 1.32/0.53  % (31963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (31963)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (31963)Memory used [KB]: 1791
% 1.32/0.53  % (31963)Time elapsed: 0.128 s
% 1.32/0.53  % (31963)------------------------------
% 1.32/0.53  % (31963)------------------------------
% 1.32/0.53  fof(f751,plain,(
% 1.32/0.53    sK2 = k4_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f750,f55])).
% 1.32/0.53  fof(f55,plain,(
% 1.32/0.53    l1_pre_topc(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f750,plain,(
% 1.32/0.53    sK2 = k4_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f749,f54])).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    v2_pre_topc(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f749,plain,(
% 1.32/0.53    sK2 = k4_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(resolution,[],[f748,f74])).
% 1.32/0.53  fof(f74,plain,(
% 1.32/0.53    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f41])).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.53    inference(flattening,[],[f40])).
% 1.32/0.53  fof(f40,plain,(
% 1.32/0.53    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,axiom,(
% 1.32/0.53    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 1.32/0.53  fof(f748,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f747,f53])).
% 1.32/0.53  fof(f747,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f746,f52])).
% 1.32/0.53  fof(f746,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f745,f55])).
% 1.32/0.53  fof(f745,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f744,f54])).
% 1.32/0.53  fof(f744,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(resolution,[],[f743,f75])).
% 1.32/0.53  fof(f75,plain,(
% 1.32/0.53    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f41])).
% 1.32/0.53  fof(f743,plain,(
% 1.32/0.53    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f742,f47])).
% 1.32/0.53  fof(f742,plain,(
% 1.32/0.53    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(subsumption_resolution,[],[f741,f49])).
% 1.32/0.53  fof(f741,plain,(
% 1.32/0.53    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(subsumption_resolution,[],[f740,f48])).
% 1.32/0.53  fof(f740,plain,(
% 1.32/0.53    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f739])).
% 1.32/0.53  fof(f739,plain,(
% 1.32/0.53    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(resolution,[],[f738,f270])).
% 1.32/0.53  fof(f270,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = X0 | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0)) )),
% 1.32/0.53    inference(resolution,[],[f267,f52])).
% 1.32/0.53  fof(f267,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | k4_tmap_1(sK0,X1) = X0 | ~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_1(X0)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f266,f53])).
% 1.32/0.53  fof(f266,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | k4_tmap_1(sK0,X1) = X0 | ~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f264,f54])).
% 1.32/0.53  fof(f264,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | k4_tmap_1(sK0,X1) = X0 | ~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,X1)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.53    inference(resolution,[],[f263,f55])).
% 1.32/0.53  fof(f263,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | k4_tmap_1(X2,X1) = X0 | ~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k4_tmap_1(X2,X1)) | ~v2_pre_topc(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X1,X2) | v2_struct_0(X2)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f262,f75])).
% 1.32/0.53  fof(f262,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X0) | ~v1_funct_2(k4_tmap_1(X2,X1),u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | k4_tmap_1(X2,X1) = X0 | ~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k4_tmap_1(X2,X1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X2)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f261])).
% 1.32/0.53  fof(f261,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X0) | ~v1_funct_2(k4_tmap_1(X2,X1),u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | k4_tmap_1(X2,X1) = X0 | ~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k4_tmap_1(X2,X1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X2)) )),
% 1.32/0.53    inference(resolution,[],[f155,f76])).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f41])).
% 1.32/0.53  fof(f155,plain,(
% 1.32/0.53    ( ! [X6,X4,X7,X5,X3] : (~m1_subset_1(k4_tmap_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | ~v1_funct_2(k4_tmap_1(X6,X7),X4,X5) | ~v1_funct_2(X3,X4,X5) | k4_tmap_1(X6,X7) = X3 | ~r2_funct_2(X4,X5,X3,k4_tmap_1(X6,X7)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(X7,X6) | v2_struct_0(X6)) )),
% 1.32/0.53    inference(resolution,[],[f82,f74])).
% 1.32/0.53  fof(f82,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_funct_2(X0,X1,X2,X3)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f45])).
% 1.32/0.53  fof(f738,plain,(
% 1.32/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f737,f53])).
% 1.32/0.53  fof(f737,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f736,f52])).
% 1.32/0.53  fof(f736,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f735,f55])).
% 1.32/0.53  fof(f735,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f734,f54])).
% 1.32/0.53  fof(f734,plain,(
% 1.32/0.53    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(resolution,[],[f733,f76])).
% 1.32/0.53  fof(f733,plain,(
% 1.32/0.53    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f732,f719])).
% 1.32/0.53  fof(f719,plain,(
% 1.32/0.53    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f718,f47])).
% 1.32/0.53  fof(f718,plain,(
% 1.32/0.53    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(subsumption_resolution,[],[f717,f49])).
% 1.32/0.53  fof(f717,plain,(
% 1.32/0.53    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(subsumption_resolution,[],[f716,f48])).
% 1.32/0.53  fof(f716,plain,(
% 1.32/0.53    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.53    inference(resolution,[],[f701,f270])).
% 1.32/0.53  fof(f701,plain,(
% 1.32/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.53    inference(subsumption_resolution,[],[f563,f700])).
% 1.32/0.53  fof(f700,plain,(
% 1.32/0.53    r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))),
% 1.32/0.53    inference(subsumption_resolution,[],[f699,f49])).
% 1.32/0.53  fof(f699,plain,(
% 1.32/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.53    inference(subsumption_resolution,[],[f698,f47])).
% 1.32/0.53  fof(f698,plain,(
% 1.32/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.53    inference(subsumption_resolution,[],[f697,f48])).
% 1.32/0.53  fof(f697,plain,(
% 1.32/0.53    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.53    inference(superposition,[],[f695,f387])).
% 1.32/0.53  fof(f387,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f386,f55])).
% 1.32/0.53  fof(f386,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_pre_topc(sK0)),
% 1.32/0.53    inference(resolution,[],[f385,f59])).
% 1.32/0.53  fof(f59,plain,(
% 1.32/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.32/0.53  fof(f385,plain,(
% 1.32/0.53    ~l1_struct_0(sK0) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f384,f88])).
% 1.32/0.53  fof(f88,plain,(
% 1.32/0.53    l1_pre_topc(sK1)),
% 1.32/0.53    inference(resolution,[],[f87,f52])).
% 1.32/0.53  fof(f87,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.32/0.53    inference(resolution,[],[f60,f55])).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.32/0.53  fof(f384,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK1)),
% 1.32/0.53    inference(resolution,[],[f383,f59])).
% 1.32/0.53  fof(f383,plain,(
% 1.32/0.53    ~l1_struct_0(sK1) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f381,f53])).
% 1.32/0.53  fof(f381,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(resolution,[],[f380,f62])).
% 1.32/0.53  fof(f62,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.53    inference(flattening,[],[f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.32/0.53  fof(f380,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f378,f51])).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    ~v2_struct_0(sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f378,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.32/0.53    inference(resolution,[],[f377,f62])).
% 1.32/0.53  fof(f377,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f376,f88])).
% 1.32/0.53  fof(f376,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_pre_topc(sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f375,f132])).
% 1.32/0.53  fof(f132,plain,(
% 1.32/0.53    m1_pre_topc(sK1,sK1)),
% 1.32/0.53    inference(resolution,[],[f130,f52])).
% 1.32/0.53  fof(f130,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f128,f54])).
% 1.32/0.53  fof(f128,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0) | ~v2_pre_topc(sK0)) )),
% 1.32/0.53    inference(resolution,[],[f127,f55])).
% 1.32/0.53  fof(f127,plain,(
% 1.32/0.53    ( ! [X6,X7] : (~l1_pre_topc(X6) | ~m1_pre_topc(X7,X6) | m1_pre_topc(X7,X7) | ~v2_pre_topc(X6)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f126])).
% 1.32/0.53  fof(f126,plain,(
% 1.32/0.53    ( ! [X6,X7] : (~l1_pre_topc(X6) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X7,X6) | m1_pre_topc(X7,X7) | ~v2_pre_topc(X6)) )),
% 1.32/0.53    inference(resolution,[],[f71,f83])).
% 1.32/0.53  fof(f83,plain,(
% 1.32/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.53    inference(equality_resolution,[],[f78])).
% 1.32/0.53  fof(f78,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f2])).
% 1.32/0.53  % (31976)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.53  fof(f71,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f39])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.53    inference(flattening,[],[f38])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,axiom,(
% 1.32/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.32/0.53  fof(f375,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1)),
% 1.32/0.53    inference(resolution,[],[f374,f61])).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f13])).
% 1.32/0.53  fof(f13,axiom,(
% 1.32/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.32/0.53  fof(f374,plain,(
% 1.32/0.53    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f373])).
% 1.32/0.53  fof(f373,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(forward_demodulation,[],[f372,f198])).
% 1.32/0.53  fof(f198,plain,(
% 1.32/0.53    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))),
% 1.32/0.53    inference(resolution,[],[f193,f132])).
% 1.32/0.53  fof(f193,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK2,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f192,f47])).
% 1.32/0.53  fof(f192,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_funct_1(sK2) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK2,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f190,f48])).
% 1.32/0.53  fof(f190,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK2,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 1.32/0.53    inference(resolution,[],[f185,f49])).
% 1.32/0.53  fof(f185,plain,(
% 1.32/0.53    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X2) | ~m1_pre_topc(X3,sK1) | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f184,f51])).
% 1.32/0.53  fof(f184,plain,(
% 1.32/0.53    ( ! [X2,X3] : (v2_struct_0(sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,sK1) | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f181,f93])).
% 1.32/0.53  fof(f93,plain,(
% 1.32/0.53    v2_pre_topc(sK1)),
% 1.32/0.53    inference(resolution,[],[f92,f52])).
% 1.32/0.53  fof(f92,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f90,f54])).
% 1.32/0.53  fof(f90,plain,(
% 1.32/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.32/0.53    inference(resolution,[],[f69,f55])).
% 1.32/0.53  fof(f69,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.53    inference(flattening,[],[f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.32/0.53  fof(f181,plain,(
% 1.32/0.53    ( ! [X2,X3] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,sK1) | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))) )),
% 1.32/0.53    inference(resolution,[],[f177,f88])).
% 1.32/0.53  fof(f177,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f176,f54])).
% 1.32/0.53  fof(f176,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | v2_struct_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f174,f53])).
% 1.32/0.53  fof(f174,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))) )),
% 1.32/0.53    inference(resolution,[],[f66,f55])).
% 1.32/0.53  fof(f66,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.53    inference(flattening,[],[f30])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,axiom,(
% 1.32/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.32/0.53  fof(f372,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f371,f49])).
% 1.32/0.53  fof(f371,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f370,f48])).
% 1.32/0.53  fof(f370,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f369,f47])).
% 1.32/0.53  fof(f369,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f368])).
% 1.32/0.53  fof(f368,plain,(
% 1.32/0.53    k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f367])).
% 1.32/0.53  fof(f367,plain,(
% 1.32/0.53    k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(superposition,[],[f58,f330])).
% 1.32/0.53  fof(f330,plain,(
% 1.32/0.53    k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f329,f55])).
% 1.32/0.53  fof(f329,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0)),
% 1.32/0.53    inference(resolution,[],[f328,f59])).
% 1.32/0.53  fof(f328,plain,(
% 1.32/0.53    ~l1_struct_0(sK0) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))),
% 1.32/0.53    inference(subsumption_resolution,[],[f327,f88])).
% 1.32/0.53  fof(f327,plain,(
% 1.32/0.53    k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK1)),
% 1.32/0.53    inference(resolution,[],[f326,f59])).
% 1.32/0.53  fof(f326,plain,(
% 1.32/0.53    ~l1_struct_0(sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~l1_struct_0(sK0)),
% 1.32/0.53    inference(subsumption_resolution,[],[f324,f53])).
% 1.32/0.53  fof(f324,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.32/0.53    inference(resolution,[],[f323,f62])).
% 1.32/0.53  fof(f323,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK0)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f321,f51])).
% 1.32/0.53  fof(f321,plain,(
% 1.32/0.53    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.32/0.53    inference(resolution,[],[f315,f62])).
% 1.32/0.53  fof(f315,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK1)) | sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))),
% 1.32/0.53    inference(forward_demodulation,[],[f314,f198])).
% 1.32/0.53  fof(f314,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))),
% 1.32/0.53    inference(subsumption_resolution,[],[f313,f48])).
% 1.32/0.53  fof(f313,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))),
% 1.32/0.53    inference(subsumption_resolution,[],[f311,f47])).
% 1.32/0.53  fof(f311,plain,(
% 1.32/0.53    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1),sK2))),
% 1.32/0.53    inference(resolution,[],[f303,f49])).
% 1.32/0.53  fof(f303,plain,(
% 1.32/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(X5) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f302,f88])).
% 1.32/0.53  fof(f302,plain,(
% 1.32/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(X5) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f288,f132])).
% 1.32/0.53  fof(f288,plain,(
% 1.32/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(X5) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2))) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f283])).
% 1.32/0.53  fof(f283,plain,(
% 1.32/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(X5) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1),u1_struct_0(sK0),X5,u1_struct_0(sK1),sK2))) )),
% 1.32/0.53    inference(resolution,[],[f260,f153])).
% 1.32/0.53  fof(f153,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f152,f48])).
% 1.32/0.53  fof(f152,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | k1_funct_1(sK2,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) )),
% 1.32/0.53    inference(resolution,[],[f150,f49])).
% 1.32/0.53  fof(f150,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2)) )),
% 1.32/0.53    inference(resolution,[],[f80,f47])).
% 1.32/0.53  fof(f80,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f43])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.32/0.53    inference(flattening,[],[f42])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.32/0.53  % (31979)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.32/0.53  fof(f260,plain,(
% 1.32/0.53    ( ! [X0,X1] : (m1_subset_1(sK3(u1_struct_0(X1),u1_struct_0(sK0),X0,u1_struct_0(sK1),sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | sK2 = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),X0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 1.32/0.53    inference(resolution,[],[f259,f61])).
% 1.32/0.53  fof(f259,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | ~v1_funct_2(X0,X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(X1) | v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(sK3(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1),sK2),X1) | sK2 = k2_partfun1(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1))) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f258,f48])).
% 1.32/0.53  fof(f258,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | v1_xboole_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(sK3(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1),sK2),X1) | sK2 = k2_partfun1(X1,u1_struct_0(sK0),X0,u1_struct_0(sK1))) )),
% 1.32/0.53    inference(resolution,[],[f204,f49])).
% 1.32/0.53  fof(f204,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | v1_xboole_0(X2) | ~v1_funct_2(sK2,X3,X0) | v1_xboole_0(X0) | m1_subset_1(sK3(X2,X0,X1,X3,sK2),X2) | sK2 = k2_partfun1(X2,X0,X1,X3)) )),
% 1.32/0.53    inference(resolution,[],[f56,f47])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X0) | ~v1_funct_2(X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(sK3(X0,X1,X2,X3,X4),X0) | k2_partfun1(X0,X1,X2,X3) = X4) )),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.32/0.53    inference(flattening,[],[f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : ((k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3)) & m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X4,X3,X1) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,X0) => (r2_hidden(X5,X3) => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5))) => k2_partfun1(X0,X1,X2,X3) = X4))))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0) | k2_partfun1(X0,X1,X2,X3) = X4) )),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.54  fof(f695,plain,(
% 1.32/0.54    ( ! [X0] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f694,f53])).
% 1.32/0.54  fof(f694,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f693,f52])).
% 1.32/0.54  fof(f693,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f692,f55])).
% 1.32/0.54  fof(f692,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f691,f54])).
% 1.32/0.54  fof(f691,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f690,f74])).
% 1.32/0.54  fof(f690,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f689,f53])).
% 1.32/0.54  fof(f689,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f688,f52])).
% 1.32/0.54  fof(f688,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f687,f55])).
% 1.32/0.54  fof(f687,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f686,f54])).
% 1.32/0.54  fof(f686,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f679,f75])).
% 1.32/0.54  fof(f679,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f678,f53])).
% 1.32/0.54  fof(f678,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f677,f52])).
% 1.32/0.54  fof(f677,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f676,f55])).
% 1.32/0.54  fof(f676,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f673,f54])).
% 1.32/0.54  fof(f673,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | r2_hidden(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f669,f76])).
% 1.32/0.54  fof(f669,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | r2_hidden(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f668,f54])).
% 1.32/0.54  fof(f668,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f666,f53])).
% 1.32/0.54  fof(f666,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1)) )),
% 1.32/0.54    inference(resolution,[],[f665,f55])).
% 1.32/0.54  fof(f665,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | r2_hidden(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f664,f51])).
% 1.32/0.54  fof(f664,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK1) | ~v2_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | r2_hidden(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2)) )),
% 1.32/0.54    inference(resolution,[],[f546,f132])).
% 1.32/0.54  fof(f546,plain,(
% 1.32/0.54    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X5,sK1) | ~l1_pre_topc(X4) | v2_struct_0(X4) | v2_struct_0(X5) | ~v2_pre_topc(X4) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4)))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | r2_hidden(sK4(X4,sK1,X5,X6,X7),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f545,f93])).
% 1.32/0.54  fof(f545,plain,(
% 1.32/0.54    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4)))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | r2_hidden(sK4(X4,sK1,X5,X6,X7),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f542,f51])).
% 1.32/0.54  fof(f542,plain,(
% 1.32/0.54    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4)))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | r2_hidden(sK4(X4,sK1,X5,X6,X7),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7)) )),
% 1.32/0.54    inference(resolution,[],[f64,f88])).
% 1.32/0.54  % (31957)Refutation not found, incomplete strategy% (31957)------------------------------
% 1.32/0.54  % (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31957)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (31957)Memory used [KB]: 10746
% 1.32/0.54  % (31957)Time elapsed: 0.113 s
% 1.32/0.54  % (31957)------------------------------
% 1.32/0.54  % (31957)------------------------------
% 1.32/0.54  fof(f64,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).
% 1.32/0.54  % (31962)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.32/0.54  fof(f563,plain,(
% 1.32/0.54    ~r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f561,f46])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 1.32/0.54    inference(cnf_transformation,[],[f20])).
% 1.32/0.54  fof(f561,plain,(
% 1.32/0.54    m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))),
% 1.32/0.54    inference(resolution,[],[f556,f101])).
% 1.32/0.54  fof(f101,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f100,f51])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    ( ! [X0] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.32/0.54    inference(resolution,[],[f98,f52])).
% 1.32/0.54  fof(f98,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f96,f53])).
% 1.32/0.54  fof(f96,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.32/0.54    inference(resolution,[],[f68,f55])).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f34])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.32/0.54  fof(f556,plain,(
% 1.32/0.54    m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))),
% 1.32/0.54    inference(subsumption_resolution,[],[f555,f49])).
% 1.32/0.54  fof(f555,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.54    inference(subsumption_resolution,[],[f554,f47])).
% 1.32/0.54  fof(f554,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.54    inference(subsumption_resolution,[],[f553,f48])).
% 1.32/0.54  fof(f553,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | m1_subset_1(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.32/0.54    inference(superposition,[],[f551,f387])).
% 1.32/0.54  fof(f551,plain,(
% 1.32/0.54    ( ! [X0] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f550,f53])).
% 1.32/0.54  fof(f550,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f549,f52])).
% 1.32/0.54  fof(f549,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f548,f55])).
% 1.32/0.54  fof(f548,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f547,f54])).
% 1.32/0.54  fof(f547,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f540,f74])).
% 1.32/0.54  fof(f540,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f539,f53])).
% 1.32/0.54  fof(f539,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f538,f52])).
% 1.32/0.54  % (31967)Refutation not found, incomplete strategy% (31967)------------------------------
% 1.32/0.54  % (31967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31967)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (31967)Memory used [KB]: 10746
% 1.32/0.54  % (31967)Time elapsed: 0.134 s
% 1.32/0.54  % (31967)------------------------------
% 1.32/0.54  % (31967)------------------------------
% 1.32/0.54  fof(f538,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f537,f55])).
% 1.32/0.54  fof(f537,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f536,f54])).
% 1.32/0.54  fof(f536,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f529,f75])).
% 1.32/0.54  fof(f529,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1))) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f528,f53])).
% 1.32/0.54  fof(f528,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f527,f52])).
% 1.32/0.54  fof(f527,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f526,f55])).
% 1.32/0.54  fof(f526,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f523,f54])).
% 1.32/0.54  fof(f523,plain,(
% 1.32/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | m1_subset_1(sK4(sK0,sK1,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X1,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f519,f76])).
% 1.32/0.54  fof(f519,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | m1_subset_1(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f518,f54])).
% 1.32/0.54  fof(f518,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f516,f53])).
% 1.32/0.54  fof(f516,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK1,sK1,X0,X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X0,sK1),X1)) )),
% 1.32/0.54    inference(resolution,[],[f515,f55])).
% 1.32/0.54  fof(f515,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | m1_subset_1(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f514,f51])).
% 1.32/0.54  fof(f514,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK1) | ~v2_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | m1_subset_1(sK4(X0,sK1,sK1,X1,X2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X1,sK1),X2)) )),
% 1.32/0.54    inference(resolution,[],[f456,f132])).
% 1.32/0.54  fof(f456,plain,(
% 1.32/0.54    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X5,sK1) | ~l1_pre_topc(X4) | v2_struct_0(X4) | v2_struct_0(X5) | ~v2_pre_topc(X4) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4)))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | m1_subset_1(sK4(X4,sK1,X5,X6,X7),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f455,f93])).
% 1.32/0.54  fof(f455,plain,(
% 1.32/0.54    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4)))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | m1_subset_1(sK4(X4,sK1,X5,X6,X7),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f452,f51])).
% 1.32/0.54  fof(f452,plain,(
% 1.32/0.54    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4)))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | m1_subset_1(sK4(X4,sK1,X5,X6,X7),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(X4),k2_tmap_1(sK1,X4,X6,X5),X7)) )),
% 1.32/0.54    inference(resolution,[],[f63,f88])).
% 1.32/0.54  fof(f63,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK4(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f732,plain,(
% 1.32/0.54    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f731])).
% 1.32/0.54  fof(f731,plain,(
% 1.32/0.54    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK2 = k4_tmap_1(sK0,sK1) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(superposition,[],[f619,f730])).
% 1.32/0.54  fof(f730,plain,(
% 1.32/0.54    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f729,f47])).
% 1.32/0.54  % (31961)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.32/0.54  fof(f729,plain,(
% 1.32/0.54    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f728,f49])).
% 1.32/0.54  fof(f728,plain,(
% 1.32/0.54    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f727,f48])).
% 1.32/0.54  fof(f727,plain,(
% 1.32/0.54    sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.54    inference(resolution,[],[f713,f270])).
% 1.32/0.54  fof(f713,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f712,f51])).
% 1.32/0.54  fof(f712,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f711,f52])).
% 1.32/0.54  fof(f711,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f708])).
% 1.32/0.54  fof(f708,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f700,f562])).
% 1.32/0.54  fof(f562,plain,(
% 1.32/0.54    ( ! [X0] : (~r2_hidden(sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,X0),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))) )),
% 1.32/0.54    inference(resolution,[],[f561,f145])).
% 1.32/0.54  fof(f145,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(X0)) | k1_funct_1(k4_tmap_1(sK0,X0),X1) = X1) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f144,f53])).
% 1.32/0.54  fof(f144,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(X0)) | k1_funct_1(k4_tmap_1(sK0,X0),X1) = X1) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f142,f54])).
% 1.32/0.54  fof(f142,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(X0)) | k1_funct_1(k4_tmap_1(sK0,X0),X1) = X1) )),
% 1.32/0.54    inference(resolution,[],[f67,f55])).
% 1.32/0.54  fof(f67,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 1.32/0.54    inference(cnf_transformation,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 1.32/0.54  fof(f619,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f618,f387])).
% 1.32/0.54  fof(f618,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f617,f53])).
% 1.32/0.54  fof(f617,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f616,f49])).
% 1.32/0.54  fof(f616,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f615,f48])).
% 1.32/0.54  fof(f615,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f614,f47])).
% 1.32/0.54  fof(f614,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f613,f132])).
% 1.32/0.54  fof(f613,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f612,f88])).
% 1.32/0.54  fof(f612,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f611,f93])).
% 1.32/0.54  fof(f611,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f610,f51])).
% 1.32/0.54  fof(f610,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f609,f55])).
% 1.32/0.54  fof(f609,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f608,f54])).
% 1.32/0.54  % (31971)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.32/0.54  fof(f608,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f607])).
% 1.32/0.54  fof(f607,plain,(
% 1.32/0.54    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(superposition,[],[f65,f572])).
% 1.32/0.54  fof(f572,plain,(
% 1.32/0.54    k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f571,f88])).
% 1.32/0.54  fof(f571,plain,(
% 1.32/0.54    sK2 = k4_tmap_1(sK0,sK1) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f570,f59])).
% 1.32/0.54  fof(f570,plain,(
% 1.32/0.54    ~l1_struct_0(sK1) | sK2 = k4_tmap_1(sK0,sK1) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f568,f51])).
% 1.32/0.54  fof(f568,plain,(
% 1.32/0.54    k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.32/0.54    inference(resolution,[],[f567,f62])).
% 1.32/0.54  fof(f567,plain,(
% 1.32/0.54    v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f566,f47])).
% 1.32/0.54  fof(f566,plain,(
% 1.32/0.54    v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f565,f49])).
% 1.32/0.54  fof(f565,plain,(
% 1.32/0.54    v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.54    inference(subsumption_resolution,[],[f564,f48])).
% 1.32/0.54  fof(f564,plain,(
% 1.32/0.54    v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.32/0.54    inference(resolution,[],[f559,f270])).
% 1.32/0.54  fof(f559,plain,(
% 1.32/0.54    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k1_funct_1(sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f556,f153])).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,sK4(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK4(X0,X1,X2,X3,X4)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | v2_struct_0(X0) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 1.32/0.54    inference(cnf_transformation,[],[f20])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (31975)------------------------------
% 1.32/0.54  % (31975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31975)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (31975)Memory used [KB]: 2430
% 1.32/0.54  % (31975)Time elapsed: 0.134 s
% 1.32/0.54  % (31975)------------------------------
% 1.32/0.54  % (31975)------------------------------
% 1.43/0.54  % (31955)Success in time 0.183 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:17 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  254 (19401 expanded)
%              Number of leaves         :   17 (3434 expanded)
%              Depth                    :   38
%              Number of atoms          : 1501 (156043 expanded)
%              Number of equality atoms :  100 (11442 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2488,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2487,f2486])).

fof(f2486,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f2096,f2485])).

fof(f2485,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2484,f2234])).

fof(f2234,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f2095,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f2095,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f2061,f54])).

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

fof(f2061,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f896,f2057])).

fof(f2057,plain,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f2028,f2056])).

fof(f2056,plain,(
    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2055,f1991])).

fof(f1991,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f1943,f1966])).

fof(f1966,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1965,f473])).

fof(f473,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f286,f187])).

fof(f187,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f112,f76])).

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

fof(f112,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f93,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,
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

fof(f286,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f285,f102])).

fof(f102,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f100,f59])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,
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

fof(f285,plain,(
    ! [X7] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f284,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f284,plain,(
    ! [X7] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f283,f96])).

fof(f96,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f57])).

fof(f95,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f94,f59])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f58])).

fof(f86,plain,
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

fof(f283,plain,(
    ! [X7] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f282,f59])).

fof(f282,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f281,f58])).

fof(f281,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f280,f57])).

fof(f280,plain,(
    ! [X7] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f279,f112])).

fof(f279,plain,(
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
    inference(subsumption_resolution,[],[f242,f111])).

fof(f111,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f110,f58])).

fof(f110,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f92,f59])).

fof(f92,plain,
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f242,plain,(
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
    inference(resolution,[],[f99,f77])).

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

fof(f99,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f57])).

fof(f98,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f59])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f87,f58])).

fof(f87,plain,
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

fof(f1965,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f669,f187])).

fof(f669,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f668,f57])).

fof(f668,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f667,f58])).

fof(f667,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f665,f59])).

fof(f665,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f307,f56])).

fof(f307,plain,(
    ! [X14,X15] :
      ( ~ m1_pre_topc(sK1,X14)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f306,f73])).

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

fof(f306,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f305,f102])).

fof(f305,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f304,f96])).

fof(f304,plain,(
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
    inference(subsumption_resolution,[],[f303,f59])).

fof(f303,plain,(
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
    inference(subsumption_resolution,[],[f302,f58])).

fof(f302,plain,(
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
    inference(subsumption_resolution,[],[f246,f57])).

fof(f246,plain,(
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
    inference(resolution,[],[f99,f81])).

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

fof(f1943,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f584,f56])).

fof(f584,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f583,f57])).

fof(f583,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f582,f58])).

fof(f582,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f580,f59])).

fof(f580,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f301,f56])).

fof(f301,plain,(
    ! [X12,X13] :
      ( ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f300,f102])).

fof(f300,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f299,f96])).

fof(f299,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f298,f59])).

fof(f298,plain,(
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
    inference(subsumption_resolution,[],[f297,f58])).

fof(f297,plain,(
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
    inference(subsumption_resolution,[],[f245,f57])).

fof(f245,plain,(
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
    inference(resolution,[],[f99,f80])).

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

fof(f2055,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2054,f2028])).

fof(f2054,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2031,f1970])).

fof(f1970,plain,(
    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f1080,f1966])).

fof(f1080,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f541,f56])).

fof(f541,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f540,f57])).

fof(f540,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f539,f58])).

fof(f539,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f537,f59])).

fof(f537,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f296,f56])).

fof(f296,plain,(
    ! [X10,X11] :
      ( ~ m1_pre_topc(sK1,X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f295,f102])).

fof(f295,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f294,f96])).

fof(f294,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f293,f59])).

fof(f293,plain,(
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
    inference(subsumption_resolution,[],[f292,f58])).

fof(f292,plain,(
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
    inference(subsumption_resolution,[],[f244,f57])).

fof(f244,plain,(
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
    inference(resolution,[],[f99,f79])).

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

fof(f2031,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1049,f2028])).

fof(f1049,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1048,f96])).

fof(f1048,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1047,f518])).

fof(f518,plain,(
    v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f481,f187])).

fof(f481,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f480,f55])).

fof(f480,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f479,f111])).

fof(f479,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f475,f112])).

fof(f475,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f291,f187])).

fof(f291,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X8)
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f290,f102])).

fof(f290,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f289,f96])).

fof(f289,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f288,f59])).

fof(f288,plain,(
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
    inference(subsumption_resolution,[],[f287,f58])).

fof(f287,plain,(
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
    inference(subsumption_resolution,[],[f243,f57])).

fof(f243,plain,(
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
    inference(resolution,[],[f99,f78])).

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

fof(f1047,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1046,f102])).

fof(f1046,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1045,f99])).

fof(f1045,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f534,f61])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f534,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f533,f55])).

fof(f533,plain,
    ( v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f532,f111])).

fof(f532,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f528,f112])).

fof(f528,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f278,f187])).

fof(f278,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f277,f102])).

fof(f277,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f276,f96])).

fof(f276,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f275,f55])).

fof(f275,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f274,f59])).

fof(f274,plain,(
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
    inference(subsumption_resolution,[],[f273,f58])).

fof(f273,plain,(
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
    inference(subsumption_resolution,[],[f241,f57])).

fof(f241,plain,(
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
    inference(resolution,[],[f99,f65])).

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

fof(f2028,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2027,f473])).

fof(f2027,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f672,f187])).

fof(f672,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f671,f55])).

fof(f671,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f670,f111])).

fof(f670,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f666,f112])).

fof(f666,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f307,f187])).

fof(f896,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f895,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f895,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f894,f55])).

fof(f894,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f893,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f893,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f887,f187])).

fof(f887,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f264,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f264,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f263,f102])).

fof(f263,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f262,f57])).

fof(f262,plain,(
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
    inference(subsumption_resolution,[],[f261,f96])).

fof(f261,plain,(
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
    inference(subsumption_resolution,[],[f260,f112])).

fof(f260,plain,(
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
    inference(subsumption_resolution,[],[f259,f111])).

fof(f259,plain,(
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
    inference(subsumption_resolution,[],[f258,f55])).

fof(f258,plain,(
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
    inference(subsumption_resolution,[],[f257,f59])).

fof(f257,plain,(
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
    inference(subsumption_resolution,[],[f239,f58])).

fof(f239,plain,(
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
    inference(resolution,[],[f99,f63])).

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

fof(f2484,plain,
    ( sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f2227,f2483])).

fof(f2483,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2481,f2095])).

fof(f2481,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2233,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f57])).

fof(f105,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f104,f55])).

fof(f104,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f58])).

fof(f89,plain,(
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

fof(f2233,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2095,f233])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f107,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f107,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f90,f59])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f56,f72])).

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

fof(f2227,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2094,f309])).

fof(f309,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f308,f102])).

fof(f308,plain,(
    ! [X16] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f247,f96])).

fof(f247,plain,(
    ! [X16] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(resolution,[],[f99,f70])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f2094,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f2059,f54])).

fof(f2059,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f868,f2057])).

fof(f868,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f867,f53])).

fof(f867,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f866,f55])).

fof(f866,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f865,f51])).

fof(f865,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f859,f187])).

fof(f859,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f256,f52])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f255,f102])).

fof(f255,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f254,f57])).

fof(f254,plain,(
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
    inference(subsumption_resolution,[],[f253,f96])).

fof(f253,plain,(
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
    inference(subsumption_resolution,[],[f252,f112])).

fof(f252,plain,(
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
    inference(subsumption_resolution,[],[f251,f111])).

fof(f251,plain,(
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
    inference(subsumption_resolution,[],[f250,f55])).

fof(f250,plain,(
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
    inference(subsumption_resolution,[],[f249,f59])).

fof(f249,plain,(
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
    inference(subsumption_resolution,[],[f238,f58])).

fof(f238,plain,(
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
    inference(resolution,[],[f99,f62])).

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

fof(f2096,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2063,f54])).

fof(f2063,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1026,f2057])).

fof(f1026,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1025,f53])).

fof(f1025,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1024,f55])).

fof(f1024,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1023,f51])).

fof(f1023,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1017,f187])).

fof(f1017,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f272,f52])).

fof(f272,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f271,f102])).

fof(f271,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f270,f57])).

fof(f270,plain,(
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
    inference(subsumption_resolution,[],[f269,f96])).

fof(f269,plain,(
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
    inference(subsumption_resolution,[],[f268,f112])).

fof(f268,plain,(
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
    inference(subsumption_resolution,[],[f267,f111])).

fof(f267,plain,(
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
    inference(subsumption_resolution,[],[f266,f55])).

fof(f266,plain,(
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
    inference(subsumption_resolution,[],[f265,f59])).

fof(f265,plain,(
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
    inference(subsumption_resolution,[],[f240,f58])).

fof(f240,plain,(
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
    inference(resolution,[],[f99,f64])).

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

fof(f2487,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2482,f2095])).

fof(f2482,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2233,f50])).

fof(f50,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12584)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (12590)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (12598)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (12606)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (12587)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (12604)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (12596)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (12588)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (12585)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (12602)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (12603)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (12597)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (12601)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (12600)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (12581)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (12583)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (12586)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (12594)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (12581)Refutation not found, incomplete strategy% (12581)------------------------------
% 0.21/0.54  % (12581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12581)Memory used [KB]: 10618
% 0.21/0.54  % (12581)Time elapsed: 0.124 s
% 0.21/0.54  % (12581)------------------------------
% 0.21/0.54  % (12581)------------------------------
% 0.21/0.54  % (12605)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (12599)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (12582)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (12592)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (12595)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (12593)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.48/0.55  % (12591)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.48/0.56  % (12589)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 2.08/0.65  % (12590)Refutation not found, incomplete strategy% (12590)------------------------------
% 2.08/0.65  % (12590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (12590)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.65  
% 2.08/0.65  % (12590)Memory used [KB]: 6140
% 2.08/0.65  % (12590)Time elapsed: 0.205 s
% 2.08/0.65  % (12590)------------------------------
% 2.08/0.65  % (12590)------------------------------
% 2.27/0.70  % (12586)Refutation found. Thanks to Tanya!
% 2.27/0.70  % SZS status Theorem for theBenchmark
% 2.27/0.70  % SZS output start Proof for theBenchmark
% 2.27/0.70  fof(f2488,plain,(
% 2.27/0.70    $false),
% 2.27/0.70    inference(subsumption_resolution,[],[f2487,f2486])).
% 2.27/0.70  fof(f2486,plain,(
% 2.27/0.70    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.70    inference(backward_demodulation,[],[f2096,f2485])).
% 2.27/0.70  fof(f2485,plain,(
% 2.27/0.70    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.70    inference(subsumption_resolution,[],[f2484,f2234])).
% 2.27/0.70  fof(f2234,plain,(
% 2.27/0.70    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.27/0.70    inference(resolution,[],[f2095,f82])).
% 2.27/0.70  fof(f82,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f49])).
% 2.27/0.70  fof(f49,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.27/0.70    inference(ennf_transformation,[],[f19])).
% 2.27/0.70  fof(f19,plain,(
% 2.27/0.70    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.27/0.70    inference(unused_predicate_definition_removal,[],[f1])).
% 2.27/0.70  fof(f1,axiom,(
% 2.27/0.70    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.27/0.70  fof(f2095,plain,(
% 2.27/0.70    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f2061,f54])).
% 2.27/0.70  fof(f54,plain,(
% 2.27/0.70    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.27/0.70    inference(cnf_transformation,[],[f21])).
% 2.27/0.70  fof(f21,plain,(
% 2.27/0.70    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/0.70    inference(flattening,[],[f20])).
% 2.27/0.70  fof(f20,plain,(
% 2.27/0.70    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f18])).
% 2.27/0.70  fof(f18,negated_conjecture,(
% 2.27/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.27/0.70    inference(negated_conjecture,[],[f17])).
% 2.27/0.70  fof(f17,conjecture,(
% 2.27/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.27/0.70  fof(f2061,plain,(
% 2.27/0.70    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.27/0.70    inference(backward_demodulation,[],[f896,f2057])).
% 2.27/0.70  fof(f2057,plain,(
% 2.27/0.70    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 2.27/0.70    inference(backward_demodulation,[],[f2028,f2056])).
% 2.27/0.70  fof(f2056,plain,(
% 2.27/0.70    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f2055,f1991])).
% 2.27/0.70  fof(f1991,plain,(
% 2.27/0.70    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.70    inference(backward_demodulation,[],[f1943,f1966])).
% 2.27/0.70  fof(f1966,plain,(
% 2.27/0.70    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(forward_demodulation,[],[f1965,f473])).
% 2.27/0.70  fof(f473,plain,(
% 2.27/0.70    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1))),
% 2.27/0.70    inference(resolution,[],[f286,f187])).
% 2.27/0.70  fof(f187,plain,(
% 2.27/0.70    m1_pre_topc(sK1,sK1)),
% 2.27/0.70    inference(resolution,[],[f112,f76])).
% 2.27/0.70  fof(f76,plain,(
% 2.27/0.70    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f42])).
% 2.27/0.70  fof(f42,plain,(
% 2.27/0.70    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.27/0.70    inference(ennf_transformation,[],[f12])).
% 2.27/0.70  fof(f12,axiom,(
% 2.27/0.70    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.27/0.70  fof(f112,plain,(
% 2.27/0.70    l1_pre_topc(sK1)),
% 2.27/0.70    inference(subsumption_resolution,[],[f93,f59])).
% 2.27/0.70  fof(f59,plain,(
% 2.27/0.70    l1_pre_topc(sK0)),
% 2.27/0.70    inference(cnf_transformation,[],[f21])).
% 2.27/0.70  fof(f93,plain,(
% 2.27/0.70    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 2.27/0.70    inference(resolution,[],[f56,f75])).
% 2.27/0.70  fof(f75,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f41])).
% 2.27/0.70  fof(f41,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/0.70    inference(ennf_transformation,[],[f6])).
% 2.27/0.70  fof(f6,axiom,(
% 2.27/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.27/0.70  fof(f56,plain,(
% 2.27/0.70    m1_pre_topc(sK1,sK0)),
% 2.27/0.70    inference(cnf_transformation,[],[f21])).
% 2.27/0.70  fof(f286,plain,(
% 2.27/0.70    ( ! [X7] : (~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f285,f102])).
% 2.27/0.70  fof(f102,plain,(
% 2.27/0.70    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.70    inference(subsumption_resolution,[],[f101,f57])).
% 2.27/0.70  fof(f57,plain,(
% 2.27/0.70    ~v2_struct_0(sK0)),
% 2.27/0.70    inference(cnf_transformation,[],[f21])).
% 2.27/0.70  fof(f101,plain,(
% 2.27/0.70    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.70    inference(subsumption_resolution,[],[f100,f59])).
% 2.27/0.70  fof(f100,plain,(
% 2.27/0.70    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.70    inference(subsumption_resolution,[],[f88,f58])).
% 2.27/0.70  fof(f58,plain,(
% 2.27/0.70    v2_pre_topc(sK0)),
% 2.27/0.70    inference(cnf_transformation,[],[f21])).
% 2.27/0.70  fof(f88,plain,(
% 2.27/0.70    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.70    inference(resolution,[],[f56,f68])).
% 2.27/0.70  fof(f68,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f29])).
% 2.27/0.70  fof(f29,plain,(
% 2.27/0.70    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.70    inference(flattening,[],[f28])).
% 2.27/0.70  fof(f28,plain,(
% 2.27/0.70    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f10])).
% 2.27/0.70  fof(f10,axiom,(
% 2.27/0.70    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.27/0.70  fof(f285,plain,(
% 2.27/0.70    ( ! [X7] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f284,f55])).
% 2.27/0.70  fof(f55,plain,(
% 2.27/0.70    ~v2_struct_0(sK1)),
% 2.27/0.70    inference(cnf_transformation,[],[f21])).
% 2.27/0.70  fof(f284,plain,(
% 2.27/0.70    ( ! [X7] : (v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f283,f96])).
% 2.27/0.70  fof(f96,plain,(
% 2.27/0.70    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f95,f57])).
% 2.27/0.70  fof(f95,plain,(
% 2.27/0.70    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f94,f59])).
% 2.27/0.70  fof(f94,plain,(
% 2.27/0.70    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f86,f58])).
% 2.27/0.70  fof(f86,plain,(
% 2.27/0.70    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(resolution,[],[f56,f66])).
% 2.27/0.70  fof(f66,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f29])).
% 2.27/0.70  fof(f283,plain,(
% 2.27/0.70    ( ! [X7] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f282,f59])).
% 2.27/0.70  fof(f282,plain,(
% 2.27/0.70    ( ! [X7] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f281,f58])).
% 2.27/0.70  fof(f281,plain,(
% 2.27/0.70    ( ! [X7] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f280,f57])).
% 2.27/0.70  fof(f280,plain,(
% 2.27/0.70    ( ! [X7] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f279,f112])).
% 2.27/0.70  fof(f279,plain,(
% 2.27/0.70    ( ! [X7] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f242,f111])).
% 2.27/0.70  fof(f111,plain,(
% 2.27/0.70    v2_pre_topc(sK1)),
% 2.27/0.70    inference(subsumption_resolution,[],[f110,f58])).
% 2.27/0.70  fof(f110,plain,(
% 2.27/0.70    ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.27/0.70    inference(subsumption_resolution,[],[f92,f59])).
% 2.27/0.70  fof(f92,plain,(
% 2.27/0.70    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.27/0.70    inference(resolution,[],[f56,f74])).
% 2.27/0.70  fof(f74,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f40])).
% 2.27/0.70  fof(f40,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.27/0.70    inference(flattening,[],[f39])).
% 2.27/0.70  fof(f39,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f5])).
% 2.27/0.70  fof(f5,axiom,(
% 2.27/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.27/0.70  fof(f242,plain,(
% 2.27/0.70    ( ! [X7] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.27/0.70    inference(resolution,[],[f99,f77])).
% 2.27/0.70  fof(f77,plain,(
% 2.27/0.70    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f44])).
% 2.27/0.70  fof(f44,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.70    inference(flattening,[],[f43])).
% 2.27/0.70  fof(f43,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f7])).
% 2.27/0.70  fof(f7,axiom,(
% 2.27/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.27/0.70  fof(f99,plain,(
% 2.27/0.70    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.70    inference(subsumption_resolution,[],[f98,f57])).
% 2.27/0.70  fof(f98,plain,(
% 2.27/0.70    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.70    inference(subsumption_resolution,[],[f97,f59])).
% 2.27/0.70  fof(f97,plain,(
% 2.27/0.70    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.70    inference(subsumption_resolution,[],[f87,f58])).
% 2.27/0.70  fof(f87,plain,(
% 2.27/0.70    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.70    inference(resolution,[],[f56,f67])).
% 2.27/0.70  fof(f67,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f29])).
% 2.27/0.70  fof(f1965,plain,(
% 2.27/0.70    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(resolution,[],[f669,f187])).
% 2.27/0.70  fof(f669,plain,(
% 2.27/0.70    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f668,f57])).
% 2.27/0.70  fof(f668,plain,(
% 2.27/0.70    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f667,f58])).
% 2.27/0.70  fof(f667,plain,(
% 2.27/0.70    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f665,f59])).
% 2.27/0.70  fof(f665,plain,(
% 2.27/0.70    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.70    inference(resolution,[],[f307,f56])).
% 2.27/0.70  fof(f307,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~m1_pre_topc(sK1,X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | v2_struct_0(X14) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f306,f73])).
% 2.27/0.70  fof(f73,plain,(
% 2.27/0.70    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f38])).
% 2.27/0.70  fof(f38,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.27/0.70    inference(flattening,[],[f37])).
% 2.27/0.70  fof(f37,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f15])).
% 2.27/0.70  fof(f15,axiom,(
% 2.27/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.27/0.70  fof(f306,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f305,f102])).
% 2.27/0.70  fof(f305,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f304,f96])).
% 2.27/0.70  fof(f304,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f303,f59])).
% 2.27/0.70  fof(f303,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f302,f58])).
% 2.27/0.70  fof(f302,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f246,f57])).
% 2.27/0.70  fof(f246,plain,(
% 2.27/0.70    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.27/0.70    inference(resolution,[],[f99,f81])).
% 2.27/0.70  fof(f81,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f48])).
% 2.27/0.70  fof(f48,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.70    inference(flattening,[],[f47])).
% 2.27/0.70  fof(f47,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f8])).
% 2.27/0.70  fof(f8,axiom,(
% 2.27/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.27/0.70  fof(f1943,plain,(
% 2.27/0.70    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.70    inference(resolution,[],[f584,f56])).
% 2.27/0.70  fof(f584,plain,(
% 2.27/0.70    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f583,f57])).
% 2.27/0.70  fof(f583,plain,(
% 2.27/0.70    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f582,f58])).
% 2.27/0.70  fof(f582,plain,(
% 2.27/0.70    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f580,f59])).
% 2.27/0.70  fof(f580,plain,(
% 2.27/0.70    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(resolution,[],[f301,f56])).
% 2.27/0.70  fof(f301,plain,(
% 2.27/0.70    ( ! [X12,X13] : (~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f300,f102])).
% 2.27/0.70  fof(f300,plain,(
% 2.27/0.70    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f299,f96])).
% 2.27/0.70  fof(f299,plain,(
% 2.27/0.70    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f298,f59])).
% 2.27/0.70  fof(f298,plain,(
% 2.27/0.70    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f297,f58])).
% 2.27/0.70  fof(f297,plain,(
% 2.27/0.70    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f245,f57])).
% 2.27/0.70  fof(f245,plain,(
% 2.27/0.70    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.27/0.70    inference(resolution,[],[f99,f80])).
% 2.27/0.70  fof(f80,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f46])).
% 2.27/0.70  fof(f46,plain,(
% 2.27/0.70    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.70    inference(flattening,[],[f45])).
% 2.27/0.70  fof(f45,plain,(
% 2.27/0.70    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f9])).
% 2.27/0.70  fof(f9,axiom,(
% 2.27/0.70    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.27/0.70  fof(f2055,plain,(
% 2.27/0.70    ~m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(forward_demodulation,[],[f2054,f2028])).
% 2.27/0.70  fof(f2054,plain,(
% 2.27/0.70    ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f2031,f1970])).
% 2.27/0.70  fof(f1970,plain,(
% 2.27/0.70    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.70    inference(backward_demodulation,[],[f1080,f1966])).
% 2.27/0.70  fof(f1080,plain,(
% 2.27/0.70    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.70    inference(resolution,[],[f541,f56])).
% 2.27/0.70  fof(f541,plain,(
% 2.27/0.70    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f540,f57])).
% 2.27/0.70  fof(f540,plain,(
% 2.27/0.70    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f539,f58])).
% 2.27/0.70  fof(f539,plain,(
% 2.27/0.70    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f537,f59])).
% 2.27/0.70  fof(f537,plain,(
% 2.27/0.70    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(resolution,[],[f296,f56])).
% 2.27/0.70  fof(f296,plain,(
% 2.27/0.70    ( ! [X10,X11] : (~m1_pre_topc(sK1,X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f295,f102])).
% 2.27/0.70  fof(f295,plain,(
% 2.27/0.70    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f294,f96])).
% 2.27/0.70  fof(f294,plain,(
% 2.27/0.70    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f293,f59])).
% 2.27/0.70  fof(f293,plain,(
% 2.27/0.70    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f292,f58])).
% 2.27/0.70  fof(f292,plain,(
% 2.27/0.70    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f244,f57])).
% 2.27/0.70  fof(f244,plain,(
% 2.27/0.70    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.27/0.70    inference(resolution,[],[f99,f79])).
% 2.27/0.70  fof(f79,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f46])).
% 2.27/0.70  fof(f2031,plain,(
% 2.27/0.70    ~v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(backward_demodulation,[],[f1049,f2028])).
% 2.27/0.70  fof(f1049,plain,(
% 2.27/0.70    ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f1048,f96])).
% 2.27/0.70  fof(f1048,plain,(
% 2.27/0.70    ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f1047,f518])).
% 2.27/0.70  fof(f518,plain,(
% 2.27/0.70    v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.27/0.70    inference(resolution,[],[f481,f187])).
% 2.27/0.70  fof(f481,plain,(
% 2.27/0.70    ( ! [X1] : (~m1_pre_topc(X1,sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f480,f55])).
% 2.27/0.70  fof(f480,plain,(
% 2.27/0.70    ( ! [X1] : (~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f479,f111])).
% 2.27/0.70  fof(f479,plain,(
% 2.27/0.70    ( ! [X1] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f475,f112])).
% 2.27/0.70  fof(f475,plain,(
% 2.27/0.70    ( ! [X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(resolution,[],[f291,f187])).
% 2.27/0.70  fof(f291,plain,(
% 2.27/0.70    ( ! [X8,X9] : (~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X8) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f290,f102])).
% 2.27/0.70  fof(f290,plain,(
% 2.27/0.70    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f289,f96])).
% 2.27/0.70  fof(f289,plain,(
% 2.27/0.70    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f288,f59])).
% 2.27/0.70  fof(f288,plain,(
% 2.27/0.70    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f287,f58])).
% 2.27/0.70  fof(f287,plain,(
% 2.27/0.70    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f243,f57])).
% 2.27/0.70  fof(f243,plain,(
% 2.27/0.70    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(resolution,[],[f99,f78])).
% 2.27/0.70  fof(f78,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f46])).
% 2.27/0.70  fof(f1047,plain,(
% 2.27/0.70    ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f1046,f102])).
% 2.27/0.70  fof(f1046,plain,(
% 2.27/0.70    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(subsumption_resolution,[],[f1045,f99])).
% 2.27/0.70  fof(f1045,plain,(
% 2.27/0.70    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.27/0.70    inference(resolution,[],[f534,f61])).
% 2.27/0.70  fof(f61,plain,(
% 2.27/0.70    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~v1_funct_1(X2)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f23])).
% 2.27/0.70  fof(f23,plain,(
% 2.27/0.70    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.27/0.70    inference(flattening,[],[f22])).
% 2.27/0.70  fof(f22,plain,(
% 2.27/0.70    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.27/0.70    inference(ennf_transformation,[],[f4])).
% 2.27/0.70  fof(f4,axiom,(
% 2.27/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.27/0.70  fof(f534,plain,(
% 2.27/0.70    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.27/0.70    inference(subsumption_resolution,[],[f533,f55])).
% 2.27/0.70  fof(f533,plain,(
% 2.27/0.70    v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.27/0.70    inference(subsumption_resolution,[],[f532,f111])).
% 2.27/0.70  fof(f532,plain,(
% 2.27/0.70    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.27/0.70    inference(subsumption_resolution,[],[f528,f112])).
% 2.27/0.70  fof(f528,plain,(
% 2.27/0.70    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.27/0.70    inference(resolution,[],[f278,f187])).
% 2.27/0.70  fof(f278,plain,(
% 2.27/0.70    ( ! [X6] : (~m1_pre_topc(sK1,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f277,f102])).
% 2.27/0.70  fof(f277,plain,(
% 2.27/0.70    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f276,f96])).
% 2.27/0.70  fof(f276,plain,(
% 2.27/0.70    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f275,f55])).
% 2.27/0.70  fof(f275,plain,(
% 2.27/0.70    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f274,f59])).
% 2.27/0.70  fof(f274,plain,(
% 2.27/0.70    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f273,f58])).
% 2.27/0.70  fof(f273,plain,(
% 2.27/0.70    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f241,f57])).
% 2.27/0.70  fof(f241,plain,(
% 2.27/0.70    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.27/0.70    inference(resolution,[],[f99,f65])).
% 2.27/0.70  fof(f65,plain,(
% 2.27/0.70    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f27])).
% 2.27/0.70  fof(f27,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.70    inference(flattening,[],[f26])).
% 2.27/0.70  fof(f26,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f14])).
% 2.27/0.70  fof(f14,axiom,(
% 2.27/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.27/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.27/0.71  fof(f2028,plain,(
% 2.27/0.71    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.71    inference(forward_demodulation,[],[f2027,f473])).
% 2.27/0.71  fof(f2027,plain,(
% 2.27/0.71    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.27/0.71    inference(resolution,[],[f672,f187])).
% 2.27/0.71  fof(f672,plain,(
% 2.27/0.71    ( ! [X1] : (~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f671,f55])).
% 2.27/0.71  fof(f671,plain,(
% 2.27/0.71    ( ! [X1] : (v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f670,f111])).
% 2.27/0.71  fof(f670,plain,(
% 2.27/0.71    ( ! [X1] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f666,f112])).
% 2.27/0.71  fof(f666,plain,(
% 2.27/0.71    ( ! [X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.27/0.71    inference(resolution,[],[f307,f187])).
% 2.27/0.71  fof(f896,plain,(
% 2.27/0.71    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f895,f53])).
% 2.27/0.71  fof(f53,plain,(
% 2.27/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.27/0.71    inference(cnf_transformation,[],[f21])).
% 2.27/0.71  fof(f895,plain,(
% 2.27/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f894,f55])).
% 2.27/0.71  fof(f894,plain,(
% 2.27/0.71    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f893,f51])).
% 2.27/0.71  fof(f51,plain,(
% 2.27/0.71    v1_funct_1(sK2)),
% 2.27/0.71    inference(cnf_transformation,[],[f21])).
% 2.27/0.71  fof(f893,plain,(
% 2.27/0.71    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f887,f187])).
% 2.27/0.71  fof(f887,plain,(
% 2.27/0.71    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(resolution,[],[f264,f52])).
% 2.27/0.71  fof(f52,plain,(
% 2.27/0.71    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.27/0.71    inference(cnf_transformation,[],[f21])).
% 2.27/0.71  fof(f264,plain,(
% 2.27/0.71    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | v2_struct_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f263,f102])).
% 2.27/0.71  fof(f263,plain,(
% 2.27/0.71    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f262,f57])).
% 2.27/0.71  fof(f262,plain,(
% 2.27/0.71    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f261,f96])).
% 2.27/0.71  fof(f261,plain,(
% 2.27/0.71    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f260,f112])).
% 2.27/0.71  fof(f260,plain,(
% 2.27/0.71    ( ! [X2,X3] : (~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f259,f111])).
% 2.27/0.71  fof(f259,plain,(
% 2.27/0.71    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f258,f55])).
% 2.27/0.71  fof(f258,plain,(
% 2.27/0.71    ( ! [X2,X3] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f257,f59])).
% 2.27/0.71  fof(f257,plain,(
% 2.27/0.71    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f239,f58])).
% 2.27/0.71  fof(f239,plain,(
% 2.27/0.71    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.27/0.71    inference(resolution,[],[f99,f63])).
% 2.27/0.71  fof(f63,plain,(
% 2.27/0.71    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.27/0.71    inference(cnf_transformation,[],[f25])).
% 2.27/0.71  fof(f25,plain,(
% 2.27/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.71    inference(flattening,[],[f24])).
% 2.27/0.71  fof(f24,plain,(
% 2.27/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.71    inference(ennf_transformation,[],[f13])).
% 2.27/0.71  fof(f13,axiom,(
% 2.27/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.27/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.27/0.71  fof(f2484,plain,(
% 2.27/0.71    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 2.27/0.71    inference(backward_demodulation,[],[f2227,f2483])).
% 2.27/0.71  fof(f2483,plain,(
% 2.27/0.71    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(subsumption_resolution,[],[f2481,f2095])).
% 2.27/0.71  fof(f2481,plain,(
% 2.27/0.71    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(resolution,[],[f2233,f106])).
% 2.27/0.71  fof(f106,plain,(
% 2.27/0.71    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f105,f57])).
% 2.27/0.71  fof(f105,plain,(
% 2.27/0.71    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f104,f55])).
% 2.27/0.71  fof(f104,plain,(
% 2.27/0.71    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f103,f59])).
% 2.27/0.71  fof(f103,plain,(
% 2.27/0.71    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f89,f58])).
% 2.27/0.71  fof(f89,plain,(
% 2.27/0.71    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.27/0.71    inference(resolution,[],[f56,f69])).
% 2.27/0.71  fof(f69,plain,(
% 2.27/0.71    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 2.27/0.71    inference(cnf_transformation,[],[f31])).
% 2.27/0.71  fof(f31,plain,(
% 2.27/0.71    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.71    inference(flattening,[],[f30])).
% 2.27/0.71  fof(f30,plain,(
% 2.27/0.71    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.71    inference(ennf_transformation,[],[f16])).
% 2.27/0.71  fof(f16,axiom,(
% 2.27/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.27/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.27/0.71  fof(f2233,plain,(
% 2.27/0.71    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))),
% 2.27/0.71    inference(resolution,[],[f2095,f233])).
% 2.27/0.71  fof(f233,plain,(
% 2.27/0.71    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.27/0.71    inference(resolution,[],[f107,f71])).
% 2.27/0.71  fof(f71,plain,(
% 2.27/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.27/0.71    inference(cnf_transformation,[],[f35])).
% 2.27/0.71  fof(f35,plain,(
% 2.27/0.71    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.27/0.71    inference(flattening,[],[f34])).
% 2.27/0.71  fof(f34,plain,(
% 2.27/0.71    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.27/0.71    inference(ennf_transformation,[],[f2])).
% 2.27/0.71  fof(f2,axiom,(
% 2.27/0.71    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.27/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.27/0.71  fof(f107,plain,(
% 2.27/0.71    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.27/0.71    inference(subsumption_resolution,[],[f90,f59])).
% 2.27/0.71  fof(f90,plain,(
% 2.27/0.71    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.27/0.71    inference(resolution,[],[f56,f72])).
% 2.27/0.71  fof(f72,plain,(
% 2.27/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.27/0.71    inference(cnf_transformation,[],[f36])).
% 2.27/0.71  fof(f36,plain,(
% 2.27/0.71    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/0.71    inference(ennf_transformation,[],[f11])).
% 2.27/0.71  fof(f11,axiom,(
% 2.27/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.27/0.71  fof(f2227,plain,(
% 2.27/0.71    v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(resolution,[],[f2094,f309])).
% 2.27/0.71  fof(f309,plain,(
% 2.27/0.71    ( ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f308,f102])).
% 2.27/0.71  fof(f308,plain,(
% 2.27/0.71    ( ! [X16] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f247,f96])).
% 2.27/0.71  fof(f247,plain,(
% 2.27/0.71    ( ! [X16] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.27/0.71    inference(resolution,[],[f99,f70])).
% 2.27/0.71  fof(f70,plain,(
% 2.27/0.71    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 2.27/0.71    inference(cnf_transformation,[],[f33])).
% 2.27/0.71  fof(f33,plain,(
% 2.27/0.71    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.27/0.71    inference(flattening,[],[f32])).
% 2.27/0.71  fof(f32,plain,(
% 2.27/0.71    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.27/0.71    inference(ennf_transformation,[],[f3])).
% 2.27/0.71  fof(f3,axiom,(
% 2.27/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.27/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 2.27/0.71  fof(f2094,plain,(
% 2.27/0.71    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.27/0.71    inference(subsumption_resolution,[],[f2059,f54])).
% 2.27/0.71  fof(f2059,plain,(
% 2.27/0.71    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.27/0.71    inference(backward_demodulation,[],[f868,f2057])).
% 2.27/0.71  fof(f868,plain,(
% 2.27/0.71    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f867,f53])).
% 2.27/0.71  fof(f867,plain,(
% 2.27/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f866,f55])).
% 2.27/0.71  fof(f866,plain,(
% 2.27/0.71    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f865,f51])).
% 2.27/0.71  fof(f865,plain,(
% 2.27/0.71    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f859,f187])).
% 2.27/0.71  fof(f859,plain,(
% 2.27/0.71    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(resolution,[],[f256,f52])).
% 2.27/0.71  fof(f256,plain,(
% 2.27/0.71    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(X1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f255,f102])).
% 2.27/0.71  fof(f255,plain,(
% 2.27/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f254,f57])).
% 2.27/0.71  fof(f254,plain,(
% 2.27/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f253,f96])).
% 2.27/0.71  fof(f253,plain,(
% 2.27/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f252,f112])).
% 2.27/0.71  fof(f252,plain,(
% 2.27/0.71    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f251,f111])).
% 2.27/0.71  fof(f251,plain,(
% 2.27/0.71    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f250,f55])).
% 2.27/0.71  fof(f250,plain,(
% 2.27/0.71    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f249,f59])).
% 2.27/0.71  fof(f249,plain,(
% 2.27/0.71    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f238,f58])).
% 2.27/0.71  fof(f238,plain,(
% 2.27/0.71    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.27/0.71    inference(resolution,[],[f99,f62])).
% 2.27/0.71  fof(f62,plain,(
% 2.27/0.71    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.27/0.71    inference(cnf_transformation,[],[f25])).
% 2.27/0.71  fof(f2096,plain,(
% 2.27/0.71    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(subsumption_resolution,[],[f2063,f54])).
% 2.27/0.71  fof(f2063,plain,(
% 2.27/0.71    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(backward_demodulation,[],[f1026,f2057])).
% 2.27/0.71  fof(f1026,plain,(
% 2.27/0.71    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f1025,f53])).
% 2.27/0.71  fof(f1025,plain,(
% 2.27/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f1024,f55])).
% 2.27/0.71  fof(f1024,plain,(
% 2.27/0.71    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f1023,f51])).
% 2.27/0.71  fof(f1023,plain,(
% 2.27/0.71    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(subsumption_resolution,[],[f1017,f187])).
% 2.27/0.71  fof(f1017,plain,(
% 2.27/0.71    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.27/0.71    inference(resolution,[],[f272,f52])).
% 2.27/0.71  fof(f272,plain,(
% 2.27/0.71    ( ! [X4,X5] : (~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(X5) | v2_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f271,f102])).
% 2.27/0.71  fof(f271,plain,(
% 2.27/0.71    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f270,f57])).
% 2.27/0.71  fof(f270,plain,(
% 2.27/0.71    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f269,f96])).
% 2.27/0.71  fof(f269,plain,(
% 2.27/0.71    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f268,f112])).
% 2.27/0.71  fof(f268,plain,(
% 2.27/0.71    ( ! [X4,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f267,f111])).
% 2.27/0.71  fof(f267,plain,(
% 2.27/0.71    ( ! [X4,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f266,f55])).
% 2.27/0.71  fof(f266,plain,(
% 2.27/0.71    ( ! [X4,X5] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f265,f59])).
% 2.27/0.71  fof(f265,plain,(
% 2.27/0.71    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(subsumption_resolution,[],[f240,f58])).
% 2.27/0.71  fof(f240,plain,(
% 2.27/0.71    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.27/0.71    inference(resolution,[],[f99,f64])).
% 2.27/0.71  fof(f64,plain,(
% 2.27/0.71    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.27/0.71    inference(cnf_transformation,[],[f25])).
% 2.27/0.71  fof(f2487,plain,(
% 2.27/0.71    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(subsumption_resolution,[],[f2482,f2095])).
% 2.27/0.71  fof(f2482,plain,(
% 2.27/0.71    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.27/0.71    inference(resolution,[],[f2233,f50])).
% 2.27/0.71  fof(f50,plain,(
% 2.27/0.71    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.27/0.71    inference(cnf_transformation,[],[f21])).
% 2.27/0.71  % SZS output end Proof for theBenchmark
% 2.27/0.71  % (12586)------------------------------
% 2.27/0.71  % (12586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.71  % (12586)Termination reason: Refutation
% 2.27/0.71  
% 2.27/0.71  % (12586)Memory used [KB]: 7547
% 2.27/0.71  % (12586)Time elapsed: 0.268 s
% 2.27/0.71  % (12586)------------------------------
% 2.27/0.71  % (12586)------------------------------
% 2.27/0.71  % (12580)Success in time 0.34 s
%------------------------------------------------------------------------------

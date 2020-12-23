%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:17 EST 2020

% Result     : Theorem 35.69s
% Output     : Refutation 35.69s
% Verified   : 
% Statistics : Number of formulae       :  315 (24409 expanded)
%              Number of leaves         :   20 (9246 expanded)
%              Depth                    :   51
%              Number of atoms          : 2186 (281583 expanded)
%              Number of equality atoms :  157 (25664 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28762,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28760,f25095])).

fof(f25095,plain,(
    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f25094,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    & ! [X3] :
        ( k1_funct_1(sK2,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(X1))
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(sK1))
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2)
        & ! [X3] :
            ( k1_funct_1(X2,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(sK1))
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
      & ! [X3] :
          ( k1_funct_1(sK2,X3) = X3
          | ~ r2_hidden(X3,u1_struct_0(sK1))
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f25094,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f25093,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f25093,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f25092,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f25092,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f25091,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f25091,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f25090,f59])).

fof(f59,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f25090,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f25089,f8887])).

fof(f8887,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f8886,f55])).

fof(f8886,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8885,f56])).

fof(f8885,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8884,f57])).

fof(f8884,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8883,f58])).

fof(f8883,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8882,f535])).

fof(f535,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f316,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f316,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f290,f57])).

fof(f290,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f8882,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8881,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f8881,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8880,f61])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8880,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8879,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f8879,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8878,f361])).

fof(f361,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f360,f55])).

fof(f360,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f359,f56])).

fof(f359,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f307,f57])).

fof(f307,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f8878,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8877,f364])).

fof(f364,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f363,f55])).

fof(f363,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f362,f56])).

fof(f362,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f308,f57])).

fof(f308,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8877,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8738,f367])).

fof(f367,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f366,f55])).

fof(f366,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f365,f56])).

fof(f365,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f309,f57])).

fof(f309,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8738,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f8640,f896])).

fof(f896,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3)
      | m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f895,f58])).

fof(f895,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0))
      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f894,f356])).

fof(f356,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f355,f56])).

fof(f355,plain,
    ( v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f304,f57])).

fof(f304,plain,
    ( v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f59,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f894,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0))
      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f891,f316])).

fof(f891,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0))
      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f354,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
                        & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f49])).

fof(f49,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
        & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f354,plain,(
    ! [X35] :
      ( ~ m1_subset_1(X35,u1_struct_0(sK1))
      | m1_subset_1(X35,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f353,f55])).

fof(f353,plain,(
    ! [X35] :
      ( m1_subset_1(X35,u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f352,f57])).

fof(f352,plain,(
    ! [X35] :
      ( m1_subset_1(X35,u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f303,f58])).

fof(f303,plain,(
    ! [X35] :
      ( m1_subset_1(X35,u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f8640,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f8639,f534])).

fof(f534,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f533,f361])).

fof(f533,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f532,f364])).

fof(f532,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f531,f367])).

fof(f531,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f530,f60])).

fof(f530,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f529,f61])).

fof(f529,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f522,f62])).

fof(f522,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f64,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
                & m1_subset_1(sK4(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
        & m1_subset_1(sK4(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

fof(f64,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f8639,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f8638,f3444])).

fof(f3444,plain,(
    k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2612,f528])).

fof(f528,plain,(
    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f527,f361])).

fof(f527,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f526,f364])).

fof(f526,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f525,f367])).

fof(f525,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f524,f60])).

fof(f524,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f523,f61])).

fof(f523,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f521,f62])).

fof(f521,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK4(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2612,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) ) ),
    inference(forward_demodulation,[],[f2611,f2290])).

fof(f2290,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) ),
    inference(forward_demodulation,[],[f2289,f1237])).

fof(f1237,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1234,f316])).

fof(f1234,plain,
    ( k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f473,f65])).

fof(f473,plain,(
    ! [X18] :
      ( ~ m1_pre_topc(X18,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) ) ),
    inference(subsumption_resolution,[],[f472,f58])).

fof(f472,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f471,f356])).

fof(f471,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f470,f316])).

fof(f470,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f469,f55])).

fof(f469,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f468,f56])).

fof(f468,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f467,f57])).

fof(f467,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f466,f60])).

fof(f466,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f395,f62])).

fof(f395,plain,(
    ! [X18] :
      ( k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))
      | ~ m1_pre_topc(X18,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f61,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f2289,plain,(
    k3_tmap_1(sK0,sK0,sK1,sK1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f2286,f316])).

fof(f2286,plain,
    ( k3_tmap_1(sK0,sK0,sK1,sK1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f1424,f65])).

fof(f1424,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1423,f56])).

fof(f1423,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ v2_pre_topc(sK0)
      | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1422,f57])).

fof(f1422,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1420,f59])).

fof(f1420,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f410,f55])).

fof(f410,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f409,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f409,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f408,f55])).

fof(f408,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f407,f56])).

fof(f407,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f406,f57])).

fof(f406,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f405,f60])).

fof(f405,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f386,f62])).

fof(f386,plain,(
    ! [X0,X1] :
      ( k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f61,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f2611,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2610,f59])).

fof(f2610,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2609,f56])).

fof(f2609,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2607,f57])).

fof(f2607,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f1264,f55])).

fof(f1264,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f1263,f478])).

fof(f478,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_pre_topc(sK1,X19)
      | ~ l1_pre_topc(X19)
      | ~ v2_pre_topc(X19)
      | v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2)) ) ),
    inference(subsumption_resolution,[],[f477,f55])).

fof(f477,plain,(
    ! [X19,X20] :
      ( v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2))
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_pre_topc(sK1,X19)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X19)
      | ~ v2_pre_topc(X19)
      | v2_struct_0(X19) ) ),
    inference(subsumption_resolution,[],[f476,f56])).

fof(f476,plain,(
    ! [X19,X20] :
      ( v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2))
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_pre_topc(sK1,X19)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X19)
      | ~ v2_pre_topc(X19)
      | v2_struct_0(X19) ) ),
    inference(subsumption_resolution,[],[f475,f57])).

fof(f475,plain,(
    ! [X19,X20] :
      ( v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2))
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_pre_topc(sK1,X19)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X19)
      | ~ v2_pre_topc(X19)
      | v2_struct_0(X19) ) ),
    inference(subsumption_resolution,[],[f474,f60])).

fof(f474,plain,(
    ! [X19,X20] :
      ( v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_pre_topc(sK1,X19)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X19)
      | ~ v2_pre_topc(X19)
      | v2_struct_0(X19) ) ),
    inference(subsumption_resolution,[],[f396,f62])).

fof(f396,plain,(
    ! [X19,X20] :
      ( v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_pre_topc(sK1,X19)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X19)
      | ~ v2_pre_topc(X19)
      | v2_struct_0(X19) ) ),
    inference(resolution,[],[f61,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f1263,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f1262,f483])).

fof(f483,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_pre_topc(sK1,X21)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f482,f55])).

fof(f482,plain,(
    ! [X21,X22] :
      ( v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0))
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_pre_topc(sK1,X21)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f481,f56])).

fof(f481,plain,(
    ! [X21,X22] :
      ( v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0))
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_pre_topc(sK1,X21)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f480,f57])).

fof(f480,plain,(
    ! [X21,X22] :
      ( v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0))
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_pre_topc(sK1,X21)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f479,f60])).

fof(f479,plain,(
    ! [X21,X22] :
      ( v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_pre_topc(sK1,X21)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f397,f62])).

fof(f397,plain,(
    ! [X21,X22] :
      ( v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_pre_topc(sK1,X21)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(resolution,[],[f61,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f44])).

fof(f1262,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f1261,f488])).

fof(f488,plain,(
    ! [X24,X23] :
      ( v2_struct_0(X23)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(sK1,X23)
      | ~ l1_pre_topc(X23)
      | ~ v2_pre_topc(X23)
      | m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f487,f55])).

fof(f487,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(sK1,X23)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X23)
      | ~ v2_pre_topc(X23)
      | v2_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f486,f56])).

fof(f486,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(sK1,X23)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X23)
      | ~ v2_pre_topc(X23)
      | v2_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f485,f57])).

fof(f485,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(sK1,X23)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X23)
      | ~ v2_pre_topc(X23)
      | v2_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f484,f60])).

fof(f484,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(sK1,X23)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X23)
      | ~ v2_pre_topc(X23)
      | v2_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f398,f62])).

fof(f398,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0))))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(sK1,X23)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X23)
      | ~ v2_pre_topc(X23)
      | v2_struct_0(X23) ) ),
    inference(resolution,[],[f61,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f44])).

fof(f1261,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f1260,f60])).

fof(f1260,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1259,f61])).

fof(f1259,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1256,f62])).

fof(f1256,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f423,f81])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ m1_subset_1(X5,X0)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f423,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ m1_pre_topc(sK1,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f422,f55])).

fof(f422,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ m1_pre_topc(sK1,X5)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f421,f56])).

fof(f421,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ m1_pre_topc(sK1,X5)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f420,f57])).

fof(f420,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ m1_pre_topc(sK1,X5)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f419,f58])).

fof(f419,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ m1_pre_topc(sK1,X5)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f418,f60])).

fof(f418,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,X5)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f388,f62])).

fof(f388,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,X5)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f61,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f8638,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f8637,f2291])).

fof(f2291,plain,(
    v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f1604,f2290])).

fof(f1604,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2)) ),
    inference(resolution,[],[f1244,f59])).

fof(f1244,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f1243,f56])).

fof(f1243,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f1242,f57])).

fof(f1242,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f1240,f59])).

fof(f1240,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) ) ),
    inference(resolution,[],[f478,f55])).

fof(f8637,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f8628,f2311])).

fof(f2311,plain,(
    v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f2049,f2290])).

fof(f2049,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1288,f59])).

fof(f1288,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1287,f56])).

fof(f1287,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1286,f57])).

fof(f1286,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1284,f59])).

fof(f1284,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f483,f55])).

fof(f8628,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(resolution,[],[f3386,f2331])).

fof(f2331,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f2166,f2290])).

fof(f2166,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f1416,f59])).

fof(f1416,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f1415,f56])).

fof(f1415,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f1414,f57])).

fof(f1414,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f1412,f59])).

fof(f1412,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f488,f55])).

fof(f3386,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f1026,f528])).

fof(f1026,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X28,u1_struct_0(sK1))
      | k1_funct_1(X27,X28) = k1_funct_1(k4_tmap_1(sK0,sK1),X28)
      | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X27,k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X27,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X27) ) ),
    inference(subsumption_resolution,[],[f1025,f361])).

fof(f1025,plain,(
    ! [X28,X27] :
      ( k1_funct_1(X27,X28) = k1_funct_1(k4_tmap_1(sK0,sK1),X28)
      | ~ m1_subset_1(X28,u1_struct_0(sK1))
      | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X27,k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X27,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X27) ) ),
    inference(subsumption_resolution,[],[f934,f367])).

fof(f934,plain,(
    ! [X28,X27] :
      ( k1_funct_1(X27,X28) = k1_funct_1(k4_tmap_1(sK0,sK1),X28)
      | ~ m1_subset_1(X28,u1_struct_0(sK1))
      | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X27,k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X27,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X27) ) ),
    inference(resolution,[],[f364,f81])).

fof(f25089,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f25086,f8771])).

fof(f8771,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f8770,f58])).

fof(f8770,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8769,f356])).

fof(f8769,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8768,f316])).

fof(f8768,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8767,f535])).

fof(f8767,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8766,f60])).

fof(f8766,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8765,f61])).

fof(f8765,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8699,f62])).

fof(f8699,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f8640,f985])).

fof(f985,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f984,f55])).

fof(f984,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f983,f56])).

fof(f983,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f982,f57])).

fof(f982,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f981,f58])).

fof(f981,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f980,f361])).

fof(f980,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f926,f367])).

fof(f926,plain,(
    ! [X12,X13] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0))
      | ~ v1_funct_1(X13)
      | ~ m1_pre_topc(sK1,X12)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f364,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f25086,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f12077,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f12077,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f8797,f12075])).

fof(f12075,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f12074,f9007])).

fof(f9007,plain,(
    k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f8778,f2612])).

fof(f8778,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f8777,f58])).

fof(f8777,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8776,f356])).

fof(f8776,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8775,f316])).

fof(f8775,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8774,f535])).

fof(f8774,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8773,f60])).

fof(f8773,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8772,f61])).

fof(f8772,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f8700,f62])).

fof(f8700,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f8640,f971])).

fof(f971,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f970,f55])).

fof(f970,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f969,f56])).

fof(f969,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f968,f57])).

fof(f968,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f967,f58])).

fof(f967,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f966,f361])).

fof(f966,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f924,f367])).

fof(f924,plain,(
    ! [X8,X9] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1))
      | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK1,X8)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f364,f70])).

fof(f12074,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f12071,f8778])).

fof(f12071,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    inference(resolution,[],[f2581,f8771])).

fof(f2581,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2580,f55])).

fof(f2580,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2579,f56])).

fof(f2579,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2578,f57])).

fof(f2578,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2577,f58])).

fof(f2577,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2576,f59])).

fof(f2576,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2575,f60])).

fof(f2575,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2574,f61])).

fof(f2574,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2573,f62])).

fof(f2573,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2569,f535])).

fof(f2569,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2566])).

fof(f2566,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f68,f2290])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
      | ~ r2_hidden(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
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
                      ( ! [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

fof(f8797,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f8796,f55])).

fof(f8796,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8795,f56])).

fof(f8795,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8794,f57])).

fof(f8794,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8793,f58])).

fof(f8793,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8792,f356])).

fof(f8792,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8791,f316])).

fof(f8791,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8790,f535])).

fof(f8790,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8789,f60])).

fof(f8789,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8788,f61])).

fof(f8788,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8787,f62])).

fof(f8787,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8786,f361])).

fof(f8786,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8785,f364])).

fof(f8785,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8705,f367])).

fof(f8705,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f8640,f247])).

fof(f247,plain,(
    ! [X70,X72,X71,X69] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(X69),k2_tmap_1(X70,X69,X71,sK1),X72)
      | k3_funct_2(u1_struct_0(X70),u1_struct_0(X69),X71,sK3(X69,X70,sK1,X71,X72)) != k1_funct_1(X72,sK3(X69,X70,sK1,X71,X72))
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X69))))
      | ~ v1_funct_2(X72,u1_struct_0(sK1),u1_struct_0(X69))
      | ~ v1_funct_1(X72)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(X69))))
      | ~ v1_funct_2(X71,u1_struct_0(X70),u1_struct_0(X69))
      | ~ v1_funct_1(X71)
      | ~ m1_pre_topc(sK1,X70)
      | ~ l1_pre_topc(X70)
      | ~ v2_pre_topc(X70)
      | v2_struct_0(X70)
      | ~ l1_pre_topc(X69)
      | ~ v2_pre_topc(X69)
      | v2_struct_0(X69) ) ),
    inference(resolution,[],[f58,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f28760,plain,(
    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f8810,f8887])).

fof(f8810,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f8809,f55])).

fof(f8809,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8808,f56])).

fof(f8808,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8807,f57])).

fof(f8807,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8806,f58])).

fof(f8806,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8805,f356])).

fof(f8805,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8804,f316])).

fof(f8804,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8803,f535])).

fof(f8803,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8802,f60])).

fof(f8802,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8801,f61])).

fof(f8801,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8800,f62])).

fof(f8800,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8799,f361])).

fof(f8799,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8798,f364])).

fof(f8798,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8706,f367])).

fof(f8706,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f8640,f618])).

fof(f618,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(X1,X0,X2,sK1),X3)
      | ~ m1_subset_1(sK3(X0,X1,sK1,X2,X3),u1_struct_0(sK0))
      | sK3(X0,X1,sK1,X2,X3) = k1_funct_1(sK2,sK3(X0,X1,sK1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f617,f58])).

fof(f617,plain,(
    ! [X2,X0,X3,X1] :
      ( sK3(X0,X1,sK1,X2,X3) = k1_funct_1(sK2,sK3(X0,X1,sK1,X2,X3))
      | ~ m1_subset_1(sK3(X0,X1,sK1,X2,X3),u1_struct_0(sK0))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(X1,X0,X2,sK1),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK1,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f63,f71])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:15:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (804388866)
% 0.12/0.36  ipcrm: permission denied for id (804421635)
% 0.12/0.37  ipcrm: permission denied for id (804552712)
% 0.12/0.37  ipcrm: permission denied for id (804618250)
% 0.12/0.37  ipcrm: permission denied for id (804651019)
% 0.12/0.38  ipcrm: permission denied for id (804683793)
% 0.12/0.38  ipcrm: permission denied for id (804749332)
% 0.12/0.39  ipcrm: permission denied for id (804814870)
% 0.12/0.39  ipcrm: permission denied for id (804847639)
% 0.20/0.39  ipcrm: permission denied for id (804880410)
% 0.20/0.39  ipcrm: permission denied for id (804913179)
% 0.20/0.40  ipcrm: permission denied for id (804945948)
% 0.20/0.40  ipcrm: permission denied for id (804978717)
% 0.20/0.40  ipcrm: permission denied for id (805044255)
% 0.20/0.41  ipcrm: permission denied for id (805109794)
% 0.20/0.41  ipcrm: permission denied for id (805142566)
% 0.20/0.42  ipcrm: permission denied for id (805208106)
% 0.20/0.42  ipcrm: permission denied for id (805273644)
% 0.20/0.42  ipcrm: permission denied for id (805306413)
% 0.20/0.43  ipcrm: permission denied for id (805371951)
% 0.20/0.43  ipcrm: permission denied for id (805404720)
% 0.20/0.43  ipcrm: permission denied for id (805437489)
% 0.20/0.43  ipcrm: permission denied for id (805470258)
% 0.20/0.43  ipcrm: permission denied for id (805503027)
% 0.20/0.44  ipcrm: permission denied for id (805568567)
% 0.20/0.44  ipcrm: permission denied for id (805666877)
% 0.20/0.45  ipcrm: permission denied for id (805699646)
% 0.20/0.45  ipcrm: permission denied for id (805830723)
% 0.20/0.45  ipcrm: permission denied for id (805863492)
% 0.20/0.45  ipcrm: permission denied for id (805896261)
% 0.20/0.46  ipcrm: permission denied for id (805929030)
% 0.20/0.46  ipcrm: permission denied for id (805961799)
% 0.20/0.46  ipcrm: permission denied for id (806027338)
% 0.20/0.46  ipcrm: permission denied for id (806092877)
% 0.20/0.47  ipcrm: permission denied for id (806125646)
% 0.20/0.47  ipcrm: permission denied for id (806191185)
% 0.20/0.48  ipcrm: permission denied for id (806322264)
% 0.20/0.48  ipcrm: permission denied for id (806387802)
% 0.20/0.48  ipcrm: permission denied for id (806453341)
% 0.20/0.49  ipcrm: permission denied for id (806518879)
% 0.20/0.49  ipcrm: permission denied for id (806584418)
% 0.20/0.49  ipcrm: permission denied for id (806617187)
% 0.20/0.50  ipcrm: permission denied for id (806715496)
% 0.20/0.50  ipcrm: permission denied for id (806748266)
% 0.20/0.50  ipcrm: permission denied for id (806781035)
% 0.20/0.51  ipcrm: permission denied for id (807010421)
% 0.20/0.51  ipcrm: permission denied for id (807108729)
% 0.35/0.52  ipcrm: permission denied for id (807239805)
% 0.35/0.52  ipcrm: permission denied for id (807272575)
% 0.37/0.59  % (15622)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.37/0.60  % (15630)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.37/0.63  % (15624)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.37/0.65  % (15632)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.37/0.65  % (15616)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.37/0.65  % (15618)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.37/0.66  % (15625)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.37/0.66  % (15634)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.37/0.66  % (15623)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.37/0.67  % (15613)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.37/0.67  % (15619)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.37/0.67  % (15614)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.37/0.67  % (15617)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.37/0.67  % (15615)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.37/0.68  % (15620)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.37/0.68  % (15621)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.37/0.68  % (15631)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.37/0.69  % (15636)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.37/0.69  % (15635)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.37/0.69  % (15633)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.37/0.69  % (15629)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.37/0.69  % (15627)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.37/0.69  % (15626)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.37/0.70  % (15628)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.37/0.71  % (15636)Refutation not found, incomplete strategy% (15636)------------------------------
% 0.37/0.71  % (15636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.71  % (15636)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.71  
% 0.37/0.71  % (15636)Memory used [KB]: 10874
% 0.37/0.71  % (15636)Time elapsed: 0.122 s
% 0.37/0.71  % (15636)------------------------------
% 0.37/0.71  % (15636)------------------------------
% 0.42/0.84  % (15635)Refutation not found, incomplete strategy% (15635)------------------------------
% 0.42/0.84  % (15635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.42/0.84  % (15635)Termination reason: Refutation not found, incomplete strategy
% 0.42/0.84  
% 0.42/0.84  % (15635)Memory used [KB]: 1918
% 0.42/0.84  % (15635)Time elapsed: 0.224 s
% 0.42/0.84  % (15635)------------------------------
% 0.42/0.84  % (15635)------------------------------
% 0.42/0.89  % (15631)Refutation not found, incomplete strategy% (15631)------------------------------
% 0.42/0.89  % (15631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.42/0.89  % (15631)Termination reason: Refutation not found, incomplete strategy
% 0.42/0.89  
% 0.42/0.89  % (15631)Memory used [KB]: 6524
% 0.42/0.89  % (15631)Time elapsed: 0.289 s
% 0.42/0.89  % (15631)------------------------------
% 0.42/0.89  % (15631)------------------------------
% 4.52/1.08  % (15620)Time limit reached!
% 4.52/1.08  % (15620)------------------------------
% 4.52/1.08  % (15620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.08  % (15620)Termination reason: Time limit
% 4.52/1.08  
% 4.52/1.08  % (15620)Memory used [KB]: 10618
% 4.52/1.08  % (15620)Time elapsed: 0.504 s
% 4.52/1.08  % (15620)------------------------------
% 4.52/1.08  % (15620)------------------------------
% 4.52/1.09  % (15625)Time limit reached!
% 4.52/1.09  % (15625)------------------------------
% 4.52/1.09  % (15625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.09  % (15625)Termination reason: Time limit
% 4.52/1.09  % (15625)Termination phase: Saturation
% 4.52/1.09  
% 4.52/1.09  % (15625)Memory used [KB]: 16375
% 4.52/1.09  % (15625)Time elapsed: 0.500 s
% 4.52/1.09  % (15625)------------------------------
% 4.52/1.09  % (15625)------------------------------
% 14.17/2.29  % (15623)Time limit reached!
% 14.17/2.29  % (15623)------------------------------
% 14.17/2.29  % (15623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.17/2.29  % (15623)Termination reason: Time limit
% 14.17/2.29  
% 14.17/2.29  % (15623)Memory used [KB]: 17014
% 14.17/2.29  % (15623)Time elapsed: 1.711 s
% 14.17/2.29  % (15623)------------------------------
% 14.17/2.29  % (15623)------------------------------
% 20.59/3.09  % (15613)Time limit reached!
% 20.59/3.09  % (15613)------------------------------
% 20.59/3.09  % (15613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.59/3.10  % (15613)Termination reason: Time limit
% 20.59/3.10  
% 20.59/3.10  % (15613)Memory used [KB]: 13944
% 20.59/3.10  % (15613)Time elapsed: 2.514 s
% 20.59/3.10  % (15613)------------------------------
% 20.59/3.10  % (15613)------------------------------
% 20.59/3.13  % (15627)Time limit reached!
% 20.59/3.13  % (15627)------------------------------
% 20.59/3.13  % (15627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.59/3.13  % (15627)Termination reason: Time limit
% 20.59/3.13  % (15627)Termination phase: Saturation
% 20.59/3.13  
% 20.59/3.13  % (15627)Memory used [KB]: 47078
% 20.59/3.13  % (15627)Time elapsed: 2.500 s
% 20.59/3.13  % (15627)------------------------------
% 20.59/3.13  % (15627)------------------------------
% 21.39/3.18  % (15629)Time limit reached!
% 21.39/3.18  % (15629)------------------------------
% 21.39/3.18  % (15629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.39/3.18  % (15629)Termination reason: Time limit
% 21.39/3.18  % (15629)Termination phase: Saturation
% 21.39/3.18  
% 21.39/3.18  % (15629)Memory used [KB]: 24818
% 21.39/3.18  % (15629)Time elapsed: 2.600 s
% 21.39/3.18  % (15629)------------------------------
% 21.39/3.18  % (15629)------------------------------
% 22.51/3.39  % (15618)Time limit reached!
% 22.51/3.39  % (15618)------------------------------
% 22.51/3.39  % (15618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.51/3.39  % (15618)Termination reason: Time limit
% 22.51/3.39  % (15618)Termination phase: Saturation
% 22.51/3.39  
% 22.51/3.39  % (15618)Memory used [KB]: 21492
% 22.51/3.39  % (15618)Time elapsed: 2.800 s
% 22.51/3.39  % (15618)------------------------------
% 22.51/3.39  % (15618)------------------------------
% 24.15/3.59  % (15616)Time limit reached!
% 24.15/3.59  % (15616)------------------------------
% 24.15/3.59  % (15616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.15/3.59  % (15616)Termination reason: Time limit
% 24.15/3.59  
% 24.15/3.59  % (15616)Memory used [KB]: 12409
% 24.15/3.59  % (15616)Time elapsed: 3.021 s
% 24.15/3.59  % (15616)------------------------------
% 24.15/3.59  % (15616)------------------------------
% 35.69/4.98  % (15624)Refutation found. Thanks to Tanya!
% 35.69/4.98  % SZS status Theorem for theBenchmark
% 35.69/5.00  % SZS output start Proof for theBenchmark
% 35.69/5.00  fof(f28762,plain,(
% 35.69/5.00    $false),
% 35.69/5.00    inference(subsumption_resolution,[],[f28760,f25095])).
% 35.69/5.00  fof(f25095,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.00    inference(subsumption_resolution,[],[f25094,f55])).
% 35.69/5.00  fof(f55,plain,(
% 35.69/5.00    ~v2_struct_0(sK0)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f48,plain,(
% 35.69/5.00    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 35.69/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f47,f46,f45])).
% 35.69/5.00  fof(f45,plain,(
% 35.69/5.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 35.69/5.00    introduced(choice_axiom,[])).
% 35.69/5.00  fof(f46,plain,(
% 35.69/5.00    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 35.69/5.00    introduced(choice_axiom,[])).
% 35.69/5.00  fof(f47,plain,(
% 35.69/5.00    ? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 35.69/5.00    introduced(choice_axiom,[])).
% 35.69/5.00  fof(f18,plain,(
% 35.69/5.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f17])).
% 35.69/5.00  fof(f17,plain,(
% 35.69/5.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f16])).
% 35.69/5.00  fof(f16,negated_conjecture,(
% 35.69/5.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 35.69/5.00    inference(negated_conjecture,[],[f15])).
% 35.69/5.00  fof(f15,conjecture,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 35.69/5.00  fof(f25094,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f25093,f56])).
% 35.69/5.00  fof(f56,plain,(
% 35.69/5.00    v2_pre_topc(sK0)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f25093,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f25092,f57])).
% 35.69/5.00  fof(f57,plain,(
% 35.69/5.00    l1_pre_topc(sK0)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f25092,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f25091,f58])).
% 35.69/5.00  fof(f58,plain,(
% 35.69/5.00    ~v2_struct_0(sK1)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f25091,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f25090,f59])).
% 35.69/5.00  fof(f59,plain,(
% 35.69/5.00    m1_pre_topc(sK1,sK0)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f25090,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f25089,f8887])).
% 35.69/5.00  fof(f8887,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8886,f55])).
% 35.69/5.00  fof(f8886,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8885,f56])).
% 35.69/5.00  fof(f8885,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8884,f57])).
% 35.69/5.00  fof(f8884,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8883,f58])).
% 35.69/5.00  fof(f8883,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8882,f535])).
% 35.69/5.00  fof(f535,plain,(
% 35.69/5.00    m1_pre_topc(sK1,sK1)),
% 35.69/5.00    inference(resolution,[],[f316,f65])).
% 35.69/5.00  fof(f65,plain,(
% 35.69/5.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f19])).
% 35.69/5.00  fof(f19,plain,(
% 35.69/5.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 35.69/5.00    inference(ennf_transformation,[],[f9])).
% 35.69/5.00  fof(f9,axiom,(
% 35.69/5.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 35.69/5.00  fof(f316,plain,(
% 35.69/5.00    l1_pre_topc(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f290,f57])).
% 35.69/5.00  fof(f290,plain,(
% 35.69/5.00    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 35.69/5.00    inference(resolution,[],[f59,f66])).
% 35.69/5.00  fof(f66,plain,(
% 35.69/5.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f20])).
% 35.69/5.00  fof(f20,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 35.69/5.00    inference(ennf_transformation,[],[f3])).
% 35.69/5.00  fof(f3,axiom,(
% 35.69/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 35.69/5.00  fof(f8882,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8881,f60])).
% 35.69/5.00  fof(f60,plain,(
% 35.69/5.00    v1_funct_1(sK2)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f8881,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8880,f61])).
% 35.69/5.00  fof(f61,plain,(
% 35.69/5.00    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f8880,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8879,f62])).
% 35.69/5.00  fof(f62,plain,(
% 35.69/5.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f8879,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8878,f361])).
% 35.69/5.00  fof(f361,plain,(
% 35.69/5.00    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f360,f55])).
% 35.69/5.00  fof(f360,plain,(
% 35.69/5.00    v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f359,f56])).
% 35.69/5.00  fof(f359,plain,(
% 35.69/5.00    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f307,f57])).
% 35.69/5.00  fof(f307,plain,(
% 35.69/5.00    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(resolution,[],[f59,f78])).
% 35.69/5.00  fof(f78,plain,(
% 35.69/5.00    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f40])).
% 35.69/5.00  fof(f40,plain,(
% 35.69/5.00    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f39])).
% 35.69/5.00  fof(f39,plain,(
% 35.69/5.00    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f8])).
% 35.69/5.00  fof(f8,axiom,(
% 35.69/5.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 35.69/5.00  fof(f8878,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8877,f364])).
% 35.69/5.00  fof(f364,plain,(
% 35.69/5.00    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 35.69/5.00    inference(subsumption_resolution,[],[f363,f55])).
% 35.69/5.00  fof(f363,plain,(
% 35.69/5.00    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f362,f56])).
% 35.69/5.00  fof(f362,plain,(
% 35.69/5.00    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f308,f57])).
% 35.69/5.00  fof(f308,plain,(
% 35.69/5.00    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(resolution,[],[f59,f79])).
% 35.69/5.00  fof(f79,plain,(
% 35.69/5.00    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f40])).
% 35.69/5.00  fof(f8877,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8738,f367])).
% 35.69/5.00  fof(f367,plain,(
% 35.69/5.00    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 35.69/5.00    inference(subsumption_resolution,[],[f366,f55])).
% 35.69/5.00  fof(f366,plain,(
% 35.69/5.00    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f365,f56])).
% 35.69/5.00  fof(f365,plain,(
% 35.69/5.00    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f309,f57])).
% 35.69/5.00  fof(f309,plain,(
% 35.69/5.00    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(resolution,[],[f59,f80])).
% 35.69/5.00  fof(f80,plain,(
% 35.69/5.00    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f40])).
% 35.69/5.00  fof(f8738,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(resolution,[],[f8640,f896])).
% 35.69/5.00  fof(f896,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3) | m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f895,f58])).
% 35.69/5.00  fof(f895,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f894,f356])).
% 35.69/5.00  fof(f356,plain,(
% 35.69/5.00    v2_pre_topc(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f355,f56])).
% 35.69/5.00  fof(f355,plain,(
% 35.69/5.00    v2_pre_topc(sK1) | ~v2_pre_topc(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f304,f57])).
% 35.69/5.00  fof(f304,plain,(
% 35.69/5.00    v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 35.69/5.00    inference(resolution,[],[f59,f76])).
% 35.69/5.00  fof(f76,plain,(
% 35.69/5.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f36])).
% 35.69/5.00  fof(f36,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 35.69/5.00    inference(flattening,[],[f35])).
% 35.69/5.00  fof(f35,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f2])).
% 35.69/5.00  fof(f2,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 35.69/5.00  fof(f894,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f891,f316])).
% 35.69/5.00  fof(f891,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,sK1,X1,X2,X3),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK1,X0,X2,X1),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(resolution,[],[f354,f70])).
% 35.69/5.00  fof(f70,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f50])).
% 35.69/5.00  fof(f50,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f49])).
% 35.69/5.00  fof(f49,plain,(
% 35.69/5.00    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 35.69/5.00    introduced(choice_axiom,[])).
% 35.69/5.00  fof(f28,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f27])).
% 35.69/5.00  fof(f27,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f10])).
% 35.69/5.00  fof(f10,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 35.69/5.00  fof(f354,plain,(
% 35.69/5.00    ( ! [X35] : (~m1_subset_1(X35,u1_struct_0(sK1)) | m1_subset_1(X35,u1_struct_0(sK0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f353,f55])).
% 35.69/5.00  fof(f353,plain,(
% 35.69/5.00    ( ! [X35] : (m1_subset_1(X35,u1_struct_0(sK0)) | ~m1_subset_1(X35,u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f352,f57])).
% 35.69/5.00  fof(f352,plain,(
% 35.69/5.00    ( ! [X35] : (m1_subset_1(X35,u1_struct_0(sK0)) | ~m1_subset_1(X35,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f303,f58])).
% 35.69/5.00  fof(f303,plain,(
% 35.69/5.00    ( ! [X35] : (m1_subset_1(X35,u1_struct_0(sK0)) | ~m1_subset_1(X35,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(resolution,[],[f59,f75])).
% 35.69/5.00  fof(f75,plain,(
% 35.69/5.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f34])).
% 35.69/5.00  fof(f34,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f33])).
% 35.69/5.00  fof(f33,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f4])).
% 35.69/5.00  fof(f4,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 35.69/5.00  fof(f8640,plain,(
% 35.69/5.00    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8639,f534])).
% 35.69/5.00  fof(f534,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))),
% 35.69/5.00    inference(subsumption_resolution,[],[f533,f361])).
% 35.69/5.00  fof(f533,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f532,f364])).
% 35.69/5.00  fof(f532,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f531,f367])).
% 35.69/5.00  fof(f531,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f530,f60])).
% 35.69/5.00  fof(f530,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f529,f61])).
% 35.69/5.00  fof(f529,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f522,f62])).
% 35.69/5.00  fof(f522,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(resolution,[],[f64,f83])).
% 35.69/5.00  fof(f83,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f54])).
% 35.69/5.00  fof(f54,plain,(
% 35.69/5.00    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.69/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).
% 35.69/5.00  fof(f53,plain,(
% 35.69/5.00    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0)))),
% 35.69/5.00    introduced(choice_axiom,[])).
% 35.69/5.00  fof(f52,plain,(
% 35.69/5.00    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.69/5.00    inference(rectify,[],[f51])).
% 35.69/5.00  fof(f51,plain,(
% 35.69/5.00    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.69/5.00    inference(nnf_transformation,[],[f42])).
% 35.69/5.00  fof(f42,plain,(
% 35.69/5.00    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.69/5.00    inference(flattening,[],[f41])).
% 35.69/5.00  fof(f41,plain,(
% 35.69/5.00    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.69/5.00    inference(ennf_transformation,[],[f1])).
% 35.69/5.00  fof(f1,axiom,(
% 35.69/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).
% 35.69/5.00  fof(f64,plain,(
% 35.69/5.00    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 35.69/5.00    inference(cnf_transformation,[],[f48])).
% 35.69/5.00  fof(f8639,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(forward_demodulation,[],[f8638,f3444])).
% 35.69/5.00  fof(f3444,plain,(
% 35.69/5.00    k1_funct_1(sK2,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))),
% 35.69/5.00    inference(resolution,[],[f2612,f528])).
% 35.69/5.00  fof(f528,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f527,f361])).
% 35.69/5.00  fof(f527,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f526,f364])).
% 35.69/5.00  fof(f526,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f525,f367])).
% 35.69/5.00  fof(f525,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f524,f60])).
% 35.69/5.00  fof(f524,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f523,f61])).
% 35.69/5.00  fof(f523,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f521,f62])).
% 35.69/5.00  fof(f521,plain,(
% 35.69/5.00    m1_subset_1(sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 35.69/5.00    inference(resolution,[],[f64,f82])).
% 35.69/5.00  fof(f82,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK4(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f54])).
% 35.69/5.00  fof(f2612,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0)) )),
% 35.69/5.00    inference(forward_demodulation,[],[f2611,f2290])).
% 35.69/5.00  fof(f2290,plain,(
% 35.69/5.00    k2_tmap_1(sK1,sK0,sK2,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)),
% 35.69/5.00    inference(forward_demodulation,[],[f2289,f1237])).
% 35.69/5.00  fof(f1237,plain,(
% 35.69/5.00    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f1234,f316])).
% 35.69/5.00  fof(f1234,plain,(
% 35.69/5.00    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 35.69/5.00    inference(resolution,[],[f473,f65])).
% 35.69/5.00  fof(f473,plain,(
% 35.69/5.00    ( ! [X18] : (~m1_pre_topc(X18,sK1) | k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f472,f58])).
% 35.69/5.00  fof(f472,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f471,f356])).
% 35.69/5.00  fof(f471,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f470,f316])).
% 35.69/5.00  fof(f470,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f469,f55])).
% 35.69/5.00  fof(f469,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f468,f56])).
% 35.69/5.00  fof(f468,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f467,f57])).
% 35.69/5.00  fof(f467,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f466,f60])).
% 35.69/5.00  fof(f466,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f395,f62])).
% 35.69/5.00  fof(f395,plain,(
% 35.69/5.00    ( ! [X18] : (k2_tmap_1(sK1,sK0,sK2,X18) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X18)) | ~m1_pre_topc(X18,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 35.69/5.00    inference(resolution,[],[f61,f73])).
% 35.69/5.00  fof(f73,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f30])).
% 35.69/5.00  fof(f30,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f29])).
% 35.69/5.00  fof(f29,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f5])).
% 35.69/5.00  fof(f5,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 35.69/5.00  fof(f2289,plain,(
% 35.69/5.00    k3_tmap_1(sK0,sK0,sK1,sK1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f2286,f316])).
% 35.69/5.00  fof(f2286,plain,(
% 35.69/5.00    k3_tmap_1(sK0,sK0,sK1,sK1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 35.69/5.00    inference(resolution,[],[f1424,f65])).
% 35.69/5.00  fof(f1424,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1423,f56])).
% 35.69/5.00  fof(f1423,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~v2_pre_topc(sK0) | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1422,f57])).
% 35.69/5.00  fof(f1422,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1420,f59])).
% 35.69/5.00  fof(f1420,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k3_tmap_1(sK0,sK0,sK1,X0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0))) )),
% 35.69/5.00    inference(resolution,[],[f410,f55])).
% 35.69/5.00  fof(f410,plain,(
% 35.69/5.00    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f409,f77])).
% 35.69/5.00  fof(f77,plain,(
% 35.69/5.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f38])).
% 35.69/5.00  fof(f38,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 35.69/5.00    inference(flattening,[],[f37])).
% 35.69/5.00  fof(f37,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f13])).
% 35.69/5.00  fof(f13,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 35.69/5.00  fof(f409,plain,(
% 35.69/5.00    ( ! [X0,X1] : (k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f408,f55])).
% 35.69/5.00  fof(f408,plain,(
% 35.69/5.00    ( ! [X0,X1] : (k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f407,f56])).
% 35.69/5.00  fof(f407,plain,(
% 35.69/5.00    ( ! [X0,X1] : (k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f406,f57])).
% 35.69/5.00  fof(f406,plain,(
% 35.69/5.00    ( ! [X0,X1] : (k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f405,f60])).
% 35.69/5.00  fof(f405,plain,(
% 35.69/5.00    ( ! [X0,X1] : (k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~v1_funct_1(sK2) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f386,f62])).
% 35.69/5.00  fof(f386,plain,(
% 35.69/5.00    ( ! [X0,X1] : (k3_tmap_1(X0,sK0,sK1,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(resolution,[],[f61,f67])).
% 35.69/5.00  fof(f67,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f22])).
% 35.69/5.00  fof(f22,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f21])).
% 35.69/5.00  fof(f21,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f6])).
% 35.69/5.00  fof(f6,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 35.69/5.00  fof(f2611,plain,(
% 35.69/5.00    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2610,f59])).
% 35.69/5.00  fof(f2610,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(sK1,sK0) | k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2609,f56])).
% 35.69/5.00  fof(f2609,plain,(
% 35.69/5.00    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2607,f57])).
% 35.69/5.00  fof(f2607,plain,(
% 35.69/5.00    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | k1_funct_1(sK2,X0) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 35.69/5.00    inference(resolution,[],[f1264,f55])).
% 35.69/5.00  fof(f1264,plain,(
% 35.69/5.00    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1263,f478])).
% 35.69/5.00  fof(f478,plain,(
% 35.69/5.00    ( ! [X19,X20] : (v2_struct_0(X19) | ~m1_pre_topc(X20,X19) | ~m1_pre_topc(sK1,X19) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f477,f55])).
% 35.69/5.00  fof(f477,plain,(
% 35.69/5.00    ( ! [X19,X20] : (v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2)) | ~m1_pre_topc(X20,X19) | ~m1_pre_topc(sK1,X19) | v2_struct_0(sK0) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f476,f56])).
% 35.69/5.00  fof(f476,plain,(
% 35.69/5.00    ( ! [X19,X20] : (v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2)) | ~m1_pre_topc(X20,X19) | ~m1_pre_topc(sK1,X19) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f475,f57])).
% 35.69/5.00  fof(f475,plain,(
% 35.69/5.00    ( ! [X19,X20] : (v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2)) | ~m1_pre_topc(X20,X19) | ~m1_pre_topc(sK1,X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f474,f60])).
% 35.69/5.00  fof(f474,plain,(
% 35.69/5.00    ( ! [X19,X20] : (v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X20,X19) | ~m1_pre_topc(sK1,X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f396,f62])).
% 35.69/5.00  fof(f396,plain,(
% 35.69/5.00    ( ! [X19,X20] : (v1_funct_1(k3_tmap_1(X19,sK0,sK1,X20,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X20,X19) | ~m1_pre_topc(sK1,X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19)) )),
% 35.69/5.00    inference(resolution,[],[f61,f84])).
% 35.69/5.00  fof(f84,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f44])).
% 35.69/5.00  fof(f44,plain,(
% 35.69/5.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f43])).
% 35.69/5.00  fof(f43,plain,(
% 35.69/5.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f7])).
% 35.69/5.00  fof(f7,axiom,(
% 35.69/5.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 35.69/5.00  fof(f1263,plain,(
% 35.69/5.00    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1262,f483])).
% 35.69/5.00  fof(f483,plain,(
% 35.69/5.00    ( ! [X21,X22] : (v2_struct_0(X21) | ~m1_pre_topc(X22,X21) | ~m1_pre_topc(sK1,X21) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21) | v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f482,f55])).
% 35.69/5.00  fof(f482,plain,(
% 35.69/5.00    ( ! [X21,X22] : (v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0)) | ~m1_pre_topc(X22,X21) | ~m1_pre_topc(sK1,X21) | v2_struct_0(sK0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21) | v2_struct_0(X21)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f481,f56])).
% 35.69/5.00  fof(f481,plain,(
% 35.69/5.00    ( ! [X21,X22] : (v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0)) | ~m1_pre_topc(X22,X21) | ~m1_pre_topc(sK1,X21) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21) | v2_struct_0(X21)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f480,f57])).
% 35.69/5.00  fof(f480,plain,(
% 35.69/5.00    ( ! [X21,X22] : (v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0)) | ~m1_pre_topc(X22,X21) | ~m1_pre_topc(sK1,X21) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21) | v2_struct_0(X21)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f479,f60])).
% 35.69/5.00  fof(f479,plain,(
% 35.69/5.00    ( ! [X21,X22] : (v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X22,X21) | ~m1_pre_topc(sK1,X21) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21) | v2_struct_0(X21)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f397,f62])).
% 35.69/5.00  fof(f397,plain,(
% 35.69/5.00    ( ! [X21,X22] : (v1_funct_2(k3_tmap_1(X21,sK0,sK1,X22,sK2),u1_struct_0(X22),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X22,X21) | ~m1_pre_topc(sK1,X21) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21) | v2_struct_0(X21)) )),
% 35.69/5.00    inference(resolution,[],[f61,f85])).
% 35.69/5.00  fof(f85,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f44])).
% 35.69/5.00  fof(f1262,plain,(
% 35.69/5.00    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1261,f488])).
% 35.69/5.00  fof(f488,plain,(
% 35.69/5.00    ( ! [X24,X23] : (v2_struct_0(X23) | ~m1_pre_topc(X24,X23) | ~m1_pre_topc(sK1,X23) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23) | m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0))))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f487,f55])).
% 35.69/5.00  fof(f487,plain,(
% 35.69/5.00    ( ! [X24,X23] : (m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0)))) | ~m1_pre_topc(X24,X23) | ~m1_pre_topc(sK1,X23) | v2_struct_0(sK0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23) | v2_struct_0(X23)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f486,f56])).
% 35.69/5.00  fof(f486,plain,(
% 35.69/5.00    ( ! [X24,X23] : (m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0)))) | ~m1_pre_topc(X24,X23) | ~m1_pre_topc(sK1,X23) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23) | v2_struct_0(X23)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f485,f57])).
% 35.69/5.00  fof(f485,plain,(
% 35.69/5.00    ( ! [X24,X23] : (m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0)))) | ~m1_pre_topc(X24,X23) | ~m1_pre_topc(sK1,X23) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23) | v2_struct_0(X23)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f484,f60])).
% 35.69/5.00  fof(f484,plain,(
% 35.69/5.00    ( ! [X24,X23] : (m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X24,X23) | ~m1_pre_topc(sK1,X23) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23) | v2_struct_0(X23)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f398,f62])).
% 35.69/5.00  fof(f398,plain,(
% 35.69/5.00    ( ! [X24,X23] : (m1_subset_1(k3_tmap_1(X23,sK0,sK1,X24,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X24,X23) | ~m1_pre_topc(sK1,X23) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23) | v2_struct_0(X23)) )),
% 35.69/5.00    inference(resolution,[],[f61,f86])).
% 35.69/5.00  fof(f86,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f44])).
% 35.69/5.00  fof(f1261,plain,(
% 35.69/5.00    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1260,f60])).
% 35.69/5.00  fof(f1260,plain,(
% 35.69/5.00    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2)) | ~v1_funct_1(sK2)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1259,f61])).
% 35.69/5.00  fof(f1259,plain,(
% 35.69/5.00    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1256,f62])).
% 35.69/5.00  fof(f1256,plain,(
% 35.69/5.00    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_funct_1(sK2,X1) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k3_tmap_1(X0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)) )),
% 35.69/5.00    inference(resolution,[],[f423,f81])).
% 35.69/5.00  fof(f81,plain,(
% 35.69/5.00    ( ! [X2,X0,X5,X3,X1] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0) | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f54])).
% 35.69/5.00  fof(f423,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~m1_pre_topc(sK1,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f422,f55])).
% 35.69/5.00  fof(f422,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f421,f56])).
% 35.69/5.00  fof(f421,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~m1_pre_topc(sK1,X5) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f420,f57])).
% 35.69/5.00  fof(f420,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~m1_pre_topc(sK1,X5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f419,f58])).
% 35.69/5.00  fof(f419,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f418,f60])).
% 35.69/5.00  fof(f418,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f388,f62])).
% 35.69/5.00  fof(f388,plain,(
% 35.69/5.00    ( ! [X5] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k3_tmap_1(X5,sK0,sK1,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 35.69/5.00    inference(resolution,[],[f61,f69])).
% 35.69/5.00  fof(f69,plain,(
% 35.69/5.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f26])).
% 35.69/5.00  fof(f26,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f25])).
% 35.69/5.00  fof(f25,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f12])).
% 35.69/5.00  fof(f12,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 35.69/5.00  fof(f8638,plain,(
% 35.69/5.00    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8637,f2291])).
% 35.69/5.00  fof(f2291,plain,(
% 35.69/5.00    v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))),
% 35.69/5.00    inference(backward_demodulation,[],[f1604,f2290])).
% 35.69/5.00  fof(f1604,plain,(
% 35.69/5.00    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2))),
% 35.69/5.00    inference(resolution,[],[f1244,f59])).
% 35.69/5.00  fof(f1244,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1243,f56])).
% 35.69/5.00  fof(f1243,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1242,f57])).
% 35.69/5.00  fof(f1242,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1240,f59])).
% 35.69/5.00  fof(f1240,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))) )),
% 35.69/5.00    inference(resolution,[],[f478,f55])).
% 35.69/5.00  fof(f8637,plain,(
% 35.69/5.00    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8628,f2311])).
% 35.69/5.00  fof(f2311,plain,(
% 35.69/5.00    v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 35.69/5.00    inference(backward_demodulation,[],[f2049,f2290])).
% 35.69/5.00  fof(f2049,plain,(
% 35.69/5.00    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 35.69/5.00    inference(resolution,[],[f1288,f59])).
% 35.69/5.00  fof(f1288,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1287,f56])).
% 35.69/5.00  fof(f1287,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1286,f57])).
% 35.69/5.00  fof(f1286,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1284,f59])).
% 35.69/5.00  fof(f1284,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,sK2),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 35.69/5.00    inference(resolution,[],[f483,f55])).
% 35.69/5.00  fof(f8628,plain,(
% 35.69/5.00    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))),
% 35.69/5.00    inference(resolution,[],[f3386,f2331])).
% 35.69/5.00  fof(f2331,plain,(
% 35.69/5.00    m1_subset_1(k2_tmap_1(sK1,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 35.69/5.00    inference(backward_demodulation,[],[f2166,f2290])).
% 35.69/5.00  fof(f2166,plain,(
% 35.69/5.00    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 35.69/5.00    inference(resolution,[],[f1416,f59])).
% 35.69/5.00  fof(f1416,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1415,f56])).
% 35.69/5.00  fof(f1415,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1414,f57])).
% 35.69/5.00  fof(f1414,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1412,f59])).
% 35.69/5.00  fof(f1412,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 35.69/5.00    inference(resolution,[],[f488,f55])).
% 35.69/5.00  fof(f3386,plain,(
% 35.69/5.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) )),
% 35.69/5.00    inference(resolution,[],[f1026,f528])).
% 35.69/5.00  fof(f1026,plain,(
% 35.69/5.00    ( ! [X28,X27] : (~m1_subset_1(X28,u1_struct_0(sK1)) | k1_funct_1(X27,X28) = k1_funct_1(k4_tmap_1(sK0,sK1),X28) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X27,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X27,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X27)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f1025,f361])).
% 35.69/5.00  fof(f1025,plain,(
% 35.69/5.00    ( ! [X28,X27] : (k1_funct_1(X27,X28) = k1_funct_1(k4_tmap_1(sK0,sK1),X28) | ~m1_subset_1(X28,u1_struct_0(sK1)) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X27,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X27,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X27)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f934,f367])).
% 35.69/5.00  fof(f934,plain,(
% 35.69/5.00    ( ! [X28,X27] : (k1_funct_1(X27,X28) = k1_funct_1(k4_tmap_1(sK0,sK1),X28) | ~m1_subset_1(X28,u1_struct_0(sK1)) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X27,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X27,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X27)) )),
% 35.69/5.00    inference(resolution,[],[f364,f81])).
% 35.69/5.00  fof(f25089,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f25086,f8771])).
% 35.69/5.00  fof(f8771,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8770,f58])).
% 35.69/5.00  fof(f8770,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8769,f356])).
% 35.69/5.00  fof(f8769,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8768,f316])).
% 35.69/5.00  fof(f8768,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8767,f535])).
% 35.69/5.00  fof(f8767,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8766,f60])).
% 35.69/5.00  fof(f8766,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8765,f61])).
% 35.69/5.00  fof(f8765,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8699,f62])).
% 35.69/5.00  fof(f8699,plain,(
% 35.69/5.00    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(resolution,[],[f8640,f985])).
% 35.69/5.00  fof(f985,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f984,f55])).
% 35.69/5.00  fof(f984,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f983,f56])).
% 35.69/5.00  fof(f983,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f982,f57])).
% 35.69/5.00  fof(f982,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f981,f58])).
% 35.69/5.00  fof(f981,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | v2_struct_0(sK1) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f980,f361])).
% 35.69/5.00  fof(f980,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | v2_struct_0(sK1) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f926,f367])).
% 35.69/5.00  fof(f926,plain,(
% 35.69/5.00    ( ! [X12,X13] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X12,sK0,X13,sK1),k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK0,X12,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK0)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK0)) | ~v1_funct_1(X13) | ~m1_pre_topc(sK1,X12) | v2_struct_0(sK1) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(resolution,[],[f364,f71])).
% 35.69/5.00  fof(f71,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f50])).
% 35.69/5.00  fof(f25086,plain,(
% 35.69/5.00    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(superposition,[],[f12077,f74])).
% 35.69/5.00  fof(f74,plain,(
% 35.69/5.00    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f32])).
% 35.69/5.00  fof(f32,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f31])).
% 35.69/5.00  fof(f31,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f14])).
% 35.69/5.00  fof(f14,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 35.69/5.00  fof(f12077,plain,(
% 35.69/5.00    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.00    inference(backward_demodulation,[],[f8797,f12075])).
% 35.69/5.00  fof(f12075,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.00    inference(forward_demodulation,[],[f12074,f9007])).
% 35.69/5.00  fof(f9007,plain,(
% 35.69/5.00    k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.00    inference(resolution,[],[f8778,f2612])).
% 35.69/5.00  fof(f8778,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8777,f58])).
% 35.69/5.00  fof(f8777,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8776,f356])).
% 35.69/5.00  fof(f8776,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8775,f316])).
% 35.69/5.00  fof(f8775,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8774,f535])).
% 35.69/5.00  fof(f8774,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8773,f60])).
% 35.69/5.00  fof(f8773,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8772,f61])).
% 35.69/5.00  fof(f8772,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8700,f62])).
% 35.69/5.00  fof(f8700,plain,(
% 35.69/5.00    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 35.69/5.00    inference(resolution,[],[f8640,f971])).
% 35.69/5.00  fof(f971,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f970,f55])).
% 35.69/5.00  fof(f970,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f969,f56])).
% 35.69/5.00  fof(f969,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f968,f57])).
% 35.69/5.00  fof(f968,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f967,f58])).
% 35.69/5.00  fof(f967,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f966,f361])).
% 35.69/5.00  fof(f966,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f924,f367])).
% 35.69/5.00  fof(f924,plain,(
% 35.69/5.00    ( ! [X8,X9] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X8,sK0,X9,sK1),k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK0,X8,sK1,X9,k4_tmap_1(sK0,sK1)),u1_struct_0(X8)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK1,X8) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(resolution,[],[f364,f70])).
% 35.69/5.00  fof(f12074,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.00    inference(subsumption_resolution,[],[f12071,f8778])).
% 35.69/5.00  fof(f12071,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 35.69/5.00    inference(resolution,[],[f2581,f8771])).
% 35.69/5.00  fof(f2581,plain,(
% 35.69/5.00    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2580,f55])).
% 35.69/5.00  fof(f2580,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2579,f56])).
% 35.69/5.00  fof(f2579,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2578,f57])).
% 35.69/5.00  fof(f2578,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2577,f58])).
% 35.69/5.00  fof(f2577,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2576,f59])).
% 35.69/5.00  fof(f2576,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2575,f60])).
% 35.69/5.00  fof(f2575,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2574,f61])).
% 35.69/5.00  fof(f2574,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2573,f62])).
% 35.69/5.00  fof(f2573,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(subsumption_resolution,[],[f2569,f535])).
% 35.69/5.00  fof(f2569,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(duplicate_literal_removal,[],[f2566])).
% 35.69/5.00  fof(f2566,plain,(
% 35.69/5.00    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0) = k1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1),X0) | ~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 35.69/5.00    inference(superposition,[],[f68,f2290])).
% 35.69/5.00  fof(f68,plain,(
% 35.69/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.00    inference(cnf_transformation,[],[f24])).
% 35.69/5.00  fof(f24,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 35.69/5.00    inference(flattening,[],[f23])).
% 35.69/5.00  fof(f23,plain,(
% 35.69/5.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 35.69/5.00    inference(ennf_transformation,[],[f11])).
% 35.69/5.00  fof(f11,axiom,(
% 35.69/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 35.69/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).
% 35.69/5.00  fof(f8797,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.00    inference(subsumption_resolution,[],[f8796,f55])).
% 35.69/5.00  fof(f8796,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8795,f56])).
% 35.69/5.00  fof(f8795,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8794,f57])).
% 35.69/5.00  fof(f8794,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8793,f58])).
% 35.69/5.00  fof(f8793,plain,(
% 35.69/5.00    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.00    inference(subsumption_resolution,[],[f8792,f356])).
% 35.69/5.01  fof(f8792,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8791,f316])).
% 35.69/5.01  fof(f8791,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8790,f535])).
% 35.69/5.01  fof(f8790,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8789,f60])).
% 35.69/5.01  fof(f8789,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8788,f61])).
% 35.69/5.01  fof(f8788,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8787,f62])).
% 35.69/5.01  fof(f8787,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8786,f361])).
% 35.69/5.01  fof(f8786,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8785,f364])).
% 35.69/5.01  fof(f8785,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8705,f367])).
% 35.69/5.01  fof(f8705,plain,(
% 35.69/5.01    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(resolution,[],[f8640,f247])).
% 35.69/5.01  fof(f247,plain,(
% 35.69/5.01    ( ! [X70,X72,X71,X69] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(X69),k2_tmap_1(X70,X69,X71,sK1),X72) | k3_funct_2(u1_struct_0(X70),u1_struct_0(X69),X71,sK3(X69,X70,sK1,X71,X72)) != k1_funct_1(X72,sK3(X69,X70,sK1,X71,X72)) | ~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X69)))) | ~v1_funct_2(X72,u1_struct_0(sK1),u1_struct_0(X69)) | ~v1_funct_1(X72) | ~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(X69)))) | ~v1_funct_2(X71,u1_struct_0(X70),u1_struct_0(X69)) | ~v1_funct_1(X71) | ~m1_pre_topc(sK1,X70) | ~l1_pre_topc(X70) | ~v2_pre_topc(X70) | v2_struct_0(X70) | ~l1_pre_topc(X69) | ~v2_pre_topc(X69) | v2_struct_0(X69)) )),
% 35.69/5.01    inference(resolution,[],[f58,f72])).
% 35.69/5.01  fof(f72,plain,(
% 35.69/5.01    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.01    inference(cnf_transformation,[],[f50])).
% 35.69/5.01  fof(f28760,plain,(
% 35.69/5.01    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.01    inference(resolution,[],[f8810,f8887])).
% 35.69/5.01  fof(f8810,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 35.69/5.01    inference(subsumption_resolution,[],[f8809,f55])).
% 35.69/5.01  fof(f8809,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8808,f56])).
% 35.69/5.01  fof(f8808,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8807,f57])).
% 35.69/5.01  fof(f8807,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8806,f58])).
% 35.69/5.01  fof(f8806,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8805,f356])).
% 35.69/5.01  fof(f8805,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8804,f316])).
% 35.69/5.01  fof(f8804,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8803,f535])).
% 35.69/5.01  fof(f8803,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8802,f60])).
% 35.69/5.01  fof(f8802,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8801,f61])).
% 35.69/5.01  fof(f8801,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8800,f62])).
% 35.69/5.01  fof(f8800,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8799,f361])).
% 35.69/5.01  fof(f8799,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8798,f364])).
% 35.69/5.01  fof(f8798,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(subsumption_resolution,[],[f8706,f367])).
% 35.69/5.01  fof(f8706,plain,(
% 35.69/5.01    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 35.69/5.01    inference(resolution,[],[f8640,f618])).
% 35.69/5.01  fof(f618,plain,(
% 35.69/5.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(X1,X0,X2,sK1),X3) | ~m1_subset_1(sK3(X0,X1,sK1,X2,X3),u1_struct_0(sK0)) | sK3(X0,X1,sK1,X2,X3) = k1_funct_1(sK2,sK3(X0,X1,sK1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.01    inference(subsumption_resolution,[],[f617,f58])).
% 35.69/5.01  fof(f617,plain,(
% 35.69/5.01    ( ! [X2,X0,X3,X1] : (sK3(X0,X1,sK1,X2,X3) = k1_funct_1(sK2,sK3(X0,X1,sK1,X2,X3)) | ~m1_subset_1(sK3(X0,X1,sK1,X2,X3),u1_struct_0(sK0)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tmap_1(X1,X0,X2,sK1),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 35.69/5.01    inference(resolution,[],[f63,f71])).
% 35.69/5.01  fof(f63,plain,(
% 35.69/5.01    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 35.69/5.01    inference(cnf_transformation,[],[f48])).
% 35.69/5.01  % SZS output end Proof for theBenchmark
% 35.69/5.01  % (15624)------------------------------
% 35.69/5.01  % (15624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.69/5.01  % (15624)Termination reason: Refutation
% 35.69/5.01  
% 35.69/5.01  % (15624)Memory used [KB]: 27888
% 35.69/5.01  % (15624)Time elapsed: 4.421 s
% 35.69/5.01  % (15624)------------------------------
% 35.69/5.01  % (15624)------------------------------
% 35.69/5.01  % (15446)Success in time 4.638 s
%------------------------------------------------------------------------------

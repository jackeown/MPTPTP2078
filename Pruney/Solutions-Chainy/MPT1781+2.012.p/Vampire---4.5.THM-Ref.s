%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:18 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  323 (9028 expanded)
%              Number of leaves         :   30 (3432 expanded)
%              Depth                    :   54
%              Number of atoms          : 2329 (102818 expanded)
%              Number of equality atoms :  170 (9507 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f204,f216,f335,f492,f1028,f1045,f1121,f1198,f1582,f3367,f3464,f3481])).

fof(f3481,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | spl4_69
    | ~ spl4_186 ),
    inference(avatar_contradiction_clause,[],[f3480])).

fof(f3480,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | spl4_69
    | ~ spl4_186 ),
    inference(subsumption_resolution,[],[f3477,f2133])).

fof(f2133,plain,
    ( k4_tmap_1(sK0,sK1) != sK2
    | ~ spl4_9
    | spl4_69 ),
    inference(backward_demodulation,[],[f1026,f2105])).

fof(f2105,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f2104,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
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

fof(f2104,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f2103,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f2103,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f2099,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f2099,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f690,f443])).

fof(f443,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f442,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f442,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f441,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f441,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f440,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f440,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f439,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f439,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f438,f56])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f438,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f437,f57])).

fof(f437,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f436,f58])).

fof(f436,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f435,f59])).

fof(f435,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f432])).

fof(f432,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f66,f427])).

fof(f427,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) ),
    inference(forward_demodulation,[],[f426,f218])).

fof(f218,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f217,f98])).

fof(f98,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f89,f54])).

fof(f89,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
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

fof(f217,plain,
    ( k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f123,f62])).

fof(f62,plain,(
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

fof(f123,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f122,f55])).

fof(f122,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f121,f97])).

fof(f97,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f96,f53])).

fof(f96,plain,
    ( v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f88,f54])).

fof(f88,plain,
    ( v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f56,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
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

fof(f121,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f98])).

fof(f120,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f119,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f118,f53])).

fof(f118,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f117,f54])).

fof(f117,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f116,f57])).

fof(f116,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f101,f58])).

fof(f101,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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

fof(f426,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) ),
    inference(subsumption_resolution,[],[f425,f98])).

fof(f425,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f341,f62])).

fof(f341,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f340,f52])).

fof(f340,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f339,f53])).

fof(f339,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f336,f54])).

fof(f336,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f136,f56])).

fof(f136,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(sK1,X9)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ m1_pre_topc(X8,sK1)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f135,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
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

fof(f135,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK1)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ m1_pre_topc(X8,X9)
      | ~ m1_pre_topc(sK1,X9)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f134,f52])).

fof(f134,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK1)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ m1_pre_topc(X8,X9)
      | ~ m1_pre_topc(sK1,X9)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f133,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK1)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ m1_pre_topc(X8,X9)
      | ~ m1_pre_topc(sK1,X9)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f132,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK1)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ m1_pre_topc(X8,X9)
      | ~ m1_pre_topc(sK1,X9)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f131,f57])).

fof(f131,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK1)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X8,X9)
      | ~ m1_pre_topc(sK1,X9)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f103,f58])).

fof(f103,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK1)
      | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X8,X9)
      | ~ m1_pre_topc(sK1,X9)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f59,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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

fof(f66,plain,(
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

fof(f690,plain,
    ( ! [X10] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k2_tmap_1(sK1,sK0,sK2,sK1))
        | k2_tmap_1(sK1,sK0,sK2,sK1) = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X10) )
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f689,f431])).

fof(f431,plain,(
    v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f229,f427])).

fof(f229,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2)) ),
    inference(resolution,[],[f224,f56])).

fof(f224,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f223,f52])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f222,f53])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f54])).

fof(f219,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f109,f52])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f108,f53])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f107,f54])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f57])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f99,f58])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f59,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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

fof(f689,plain,
    ( ! [X10] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k2_tmap_1(sK1,sK0,sK2,sK1))
        | k2_tmap_1(sK1,sK0,sK2,sK1) = X10
        | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X10) )
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f656,f429])).

fof(f429,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f258,f427])).

fof(f258,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl4_9
  <=> v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f656,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k2_tmap_1(sK1,sK0,sK2,sK1))
      | k2_tmap_1(sK1,sK0,sK2,sK1) = X10
      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X10) ) ),
    inference(resolution,[],[f430,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f430,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f243,f427])).

fof(f243,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f236,f56])).

fof(f236,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f235,f52])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f53])).

fof(f234,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f54])).

fof(f231,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f115,f56])).

fof(f115,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(sK1,X2)
      | ~ m1_pre_topc(X3,X2)
      | m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f114,f52])).

fof(f114,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f113,f53])).

fof(f113,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f112,f54])).

fof(f112,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f111,f57])).

fof(f111,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f100,f58])).

fof(f100,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f59,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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

fof(f1026,plain,
    ( k4_tmap_1(sK0,sK1) != k2_tmap_1(sK1,sK0,sK2,sK1)
    | spl4_69 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1025,plain,
    ( spl4_69
  <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f3477,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_186 ),
    inference(subsumption_resolution,[],[f3476,f59])).

fof(f3476,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_186 ),
    inference(subsumption_resolution,[],[f3475,f58])).

fof(f3475,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_186 ),
    inference(subsumption_resolution,[],[f3474,f57])).

fof(f3474,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_186 ),
    inference(resolution,[],[f3366,f203])).

fof(f203,plain,
    ( ! [X10] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = X10 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_7
  <=> ! [X10] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f3366,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ spl4_186 ),
    inference(avatar_component_clause,[],[f3364])).

fof(f3364,plain,
    ( spl4_186
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f3464,plain,
    ( ~ spl4_68
    | ~ spl4_70
    | spl4_185 ),
    inference(avatar_contradiction_clause,[],[f3463])).

fof(f3463,plain,
    ( $false
    | ~ spl4_68
    | ~ spl4_70
    | spl4_185 ),
    inference(subsumption_resolution,[],[f3462,f52])).

fof(f3462,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_68
    | ~ spl4_70
    | spl4_185 ),
    inference(subsumption_resolution,[],[f3461,f53])).

fof(f3461,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_68
    | ~ spl4_70
    | spl4_185 ),
    inference(subsumption_resolution,[],[f3460,f54])).

fof(f3460,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_68
    | ~ spl4_70
    | spl4_185 ),
    inference(subsumption_resolution,[],[f3456,f3362])).

fof(f3362,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | spl4_185 ),
    inference(avatar_component_clause,[],[f3360])).

fof(f3360,plain,
    ( spl4_185
  <=> sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_185])])).

fof(f3456,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(resolution,[],[f3452,f56])).

fof(f3452,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK1,X1)
        | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X1,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f1202,f1030])).

fof(f1030,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f1029,f55])).

fof(f1029,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_68 ),
    inference(resolution,[],[f1023,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
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

fof(f1023,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1021,plain,
    ( spl4_68
  <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1202,plain,
    ( ! [X1] :
        ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X1,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X1))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f1189,f55])).

fof(f1189,plain,
    ( ! [X1] :
        ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X1,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X1))
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl4_70 ),
    inference(resolution,[],[f1044,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
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

fof(f1044,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1042,plain,
    ( spl4_70
  <=> r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f3367,plain,
    ( ~ spl4_185
    | spl4_186
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f3358,f1195,f1042,f1021,f468,f257,f155,f3364,f3360])).

fof(f155,plain,
    ( spl4_1
  <=> v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f468,plain,
    ( spl4_27
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1195,plain,
    ( spl4_72
  <=> sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f3358,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f3357,f2105])).

fof(f3357,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3356,f52])).

fof(f3356,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3355,f53])).

fof(f3355,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3354,f54])).

fof(f3354,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3353,f97])).

fof(f3353,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3352,f98])).

fof(f3352,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3351,f55])).

fof(f3351,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3350,f469])).

fof(f469,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f468])).

fof(f3350,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3349,f57])).

fof(f3349,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3348,f58])).

fof(f3348,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3347,f59])).

fof(f3347,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3346,f92])).

fof(f92,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f91,f52])).

fof(f91,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f53])).

fof(f90,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f54])).

fof(f85,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k4_tmap_1(X0,X1))
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

fof(f3346,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3345,f156])).

fof(f156,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f3345,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f3344,f95])).

fof(f95,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f94,f52])).

fof(f94,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f93,f53])).

fof(f93,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f86,f54])).

fof(f86,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3344,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(duplicate_literal_removal,[],[f3343])).

fof(f3343,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(superposition,[],[f69,f3031])).

fof(f3031,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f3030,f1197])).

fof(f1197,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f1195])).

fof(f3030,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f3029,f2121])).

fof(f2121,plain,
    ( sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f427,f2105])).

fof(f3029,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f3028,f52])).

fof(f3028,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f3027,f53])).

fof(f3027,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f3023,f54])).

fof(f3023,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(resolution,[],[f1201,f56])).

fof(f1201,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f1200,f55])).

fof(f1200,plain,
    ( ! [X0] :
        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_27
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f1199,f469])).

fof(f1199,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,sK1)
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_68
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f1188,f1023])).

fof(f1188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK1,sK1)
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_70 ),
    inference(resolution,[],[f1044,f130])).

fof(f130,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f129,f74])).

fof(f129,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ m1_pre_topc(sK1,X7)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f128,f52])).

fof(f128,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ m1_pre_topc(sK1,X7)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f127,f53])).

fof(f127,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ m1_pre_topc(sK1,X7)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ m1_pre_topc(sK1,X7)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f125,f55])).

fof(f125,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f102,f58])).

fof(f102,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_pre_topc(X6,sK1)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f59,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ r2_hidden(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
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

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
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

fof(f1582,plain,
    ( ~ spl4_68
    | spl4_71 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | ~ spl4_68
    | spl4_71 ),
    inference(subsumption_resolution,[],[f1580,f52])).

fof(f1580,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_68
    | spl4_71 ),
    inference(subsumption_resolution,[],[f1579,f54])).

fof(f1579,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_68
    | spl4_71 ),
    inference(subsumption_resolution,[],[f1575,f1193])).

fof(f1193,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f1191])).

fof(f1191,plain,
    ( spl4_71
  <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1575,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_68 ),
    inference(resolution,[],[f1030,f56])).

fof(f1198,plain,
    ( ~ spl4_71
    | spl4_72
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f1187,f1042,f1195,f1191])).

fof(f1187,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_70 ),
    inference(resolution,[],[f1044,f60])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1121,plain,
    ( ~ spl4_7
    | ~ spl4_69 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1085,f140])).

fof(f140,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f139,f57])).

fof(f139,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f105,f58])).

fof(f105,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f59,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1085,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(backward_demodulation,[],[f61,f1084])).

fof(f1084,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1083,f59])).

fof(f1083,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1082,f58])).

fof(f1082,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1081,f57])).

fof(f1081,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(resolution,[],[f1052,f203])).

fof(f1052,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ spl4_69 ),
    inference(backward_demodulation,[],[f443,f1027])).

fof(f1027,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f61,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f1045,plain,
    ( spl4_70
    | spl4_69
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f1040,f468,f257,f202,f155,f1025,f1042])).

fof(f1040,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1039,f55])).

fof(f1039,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1038,f97])).

fof(f1038,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1037,f98])).

fof(f1037,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1036,f469])).

fof(f1036,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1035,f57])).

fof(f1035,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1034,f58])).

fof(f1034,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1033,f59])).

fof(f1033,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1032,f431])).

fof(f1032,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1031,f429])).

fof(f1031,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f649,f430])).

fof(f649,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f648,f52])).

fof(f648,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f647,f53])).

fof(f647,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f646,f54])).

fof(f646,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f645,f55])).

fof(f645,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f644,f92])).

fof(f644,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f643,f156])).

fof(f643,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f635,f95])).

fof(f635,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1)
        | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK1,X2)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f203,f68])).

fof(f68,plain,(
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

fof(f1028,plain,
    ( spl4_68
    | spl4_69
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f1019,f468,f257,f202,f155,f1025,f1021])).

fof(f1019,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1018,f55])).

fof(f1018,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1017,f97])).

fof(f1017,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1016,f98])).

fof(f1016,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1015,f469])).

fof(f1015,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1014,f57])).

fof(f1014,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1013,f58])).

fof(f1013,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1012,f59])).

fof(f1012,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1011,f431])).

fof(f1011,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1010,f429])).

fof(f1010,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f642,f430])).

fof(f642,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f641,f52])).

fof(f641,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f640,f53])).

fof(f640,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f639,f54])).

fof(f639,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f638,f55])).

fof(f638,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f637,f92])).

fof(f637,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f636,f156])).

fof(f636,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f634,f95])).

fof(f634,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1)
        | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f203,f67])).

fof(f67,plain,(
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

fof(f492,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f490,f98])).

fof(f490,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_27 ),
    inference(resolution,[],[f470,f62])).

fof(f470,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f468])).

fof(f335,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f333,f52])).

fof(f333,plain,
    ( v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f332,f53])).

fof(f332,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f331,f54])).

fof(f331,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f330,f56])).

fof(f330,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f329,f57])).

fof(f329,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f328,f58])).

fof(f328,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f327,f59])).

fof(f327,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(duplicate_literal_removal,[],[f326])).

fof(f326,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(resolution,[],[f259,f81])).

fof(f81,plain,(
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

fof(f259,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f257])).

fof(f216,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f214,f52])).

fof(f214,plain,
    ( v2_struct_0(sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f213,f53])).

fof(f213,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f212,f54])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f211,f56])).

fof(f211,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_1 ),
    inference(resolution,[],[f157,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f157,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f204,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_split_clause,[],[f200,f202,f155])).

fof(f200,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1))
      | k4_tmap_1(sK0,sK1) = X10
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f148,f92])).

fof(f148,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1))
      | k4_tmap_1(sK0,sK1) = X10
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X10) ) ),
    inference(resolution,[],[f95,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (10293)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (10290)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (10301)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (10299)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (10309)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (10289)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10294)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (10300)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.20/0.51  % (10306)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.20/0.51  % (10291)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.20/0.51  % (10303)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.20/0.52  % (10298)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.52  % (10297)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.20/0.52  % (10295)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.20/0.52  % (10292)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.20/0.52  % (10296)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.20/0.52  % (10308)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.31/0.53  % (10288)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.31/0.53  % (10304)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.31/0.53  % (10312)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.31/0.53  % (10310)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.31/0.53  % (10302)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.53  % (10305)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.31/0.54  % (10311)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.31/0.54  % (10307)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.31/0.55  % (10313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.10/0.64  % (10297)Refutation not found, incomplete strategy% (10297)------------------------------
% 2.10/0.64  % (10297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.64  % (10297)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.64  
% 2.10/0.64  % (10297)Memory used [KB]: 6140
% 2.10/0.64  % (10297)Time elapsed: 0.194 s
% 2.10/0.64  % (10297)------------------------------
% 2.10/0.64  % (10297)------------------------------
% 2.10/0.65  % (10289)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.66  % SZS output start Proof for theBenchmark
% 2.10/0.66  fof(f3482,plain,(
% 2.10/0.66    $false),
% 2.10/0.66    inference(avatar_sat_refutation,[],[f204,f216,f335,f492,f1028,f1045,f1121,f1198,f1582,f3367,f3464,f3481])).
% 2.10/0.66  fof(f3481,plain,(
% 2.10/0.66    ~spl4_7 | ~spl4_9 | spl4_69 | ~spl4_186),
% 2.10/0.66    inference(avatar_contradiction_clause,[],[f3480])).
% 2.10/0.66  fof(f3480,plain,(
% 2.10/0.66    $false | (~spl4_7 | ~spl4_9 | spl4_69 | ~spl4_186)),
% 2.10/0.66    inference(subsumption_resolution,[],[f3477,f2133])).
% 2.10/0.66  fof(f2133,plain,(
% 2.10/0.66    k4_tmap_1(sK0,sK1) != sK2 | (~spl4_9 | spl4_69)),
% 2.10/0.66    inference(backward_demodulation,[],[f1026,f2105])).
% 2.10/0.66  fof(f2105,plain,(
% 2.10/0.66    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~spl4_9),
% 2.10/0.66    inference(subsumption_resolution,[],[f2104,f57])).
% 2.10/0.66  fof(f57,plain,(
% 2.10/0.66    v1_funct_1(sK2)),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f48,plain,(
% 2.10/0.66    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.10/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f47,f46,f45])).
% 2.10/0.66  fof(f45,plain,(
% 2.10/0.66    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.10/0.66    introduced(choice_axiom,[])).
% 2.10/0.66  fof(f46,plain,(
% 2.10/0.66    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 2.10/0.66    introduced(choice_axiom,[])).
% 2.10/0.66  fof(f47,plain,(
% 2.10/0.66    ? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 2.10/0.66    introduced(choice_axiom,[])).
% 2.10/0.66  fof(f18,plain,(
% 2.10/0.66    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/0.66    inference(flattening,[],[f17])).
% 2.10/0.66  fof(f17,plain,(
% 2.10/0.66    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f16])).
% 2.10/0.66  fof(f16,negated_conjecture,(
% 2.10/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.10/0.66    inference(negated_conjecture,[],[f15])).
% 2.10/0.66  fof(f15,conjecture,(
% 2.10/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.10/0.66  fof(f2104,plain,(
% 2.10/0.66    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~v1_funct_1(sK2) | ~spl4_9),
% 2.10/0.66    inference(subsumption_resolution,[],[f2103,f58])).
% 2.10/0.66  fof(f58,plain,(
% 2.10/0.66    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f2103,plain,(
% 2.10/0.66    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~spl4_9),
% 2.10/0.66    inference(subsumption_resolution,[],[f2099,f59])).
% 2.10/0.66  fof(f59,plain,(
% 2.10/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f2099,plain,(
% 2.10/0.66    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~spl4_9),
% 2.10/0.66    inference(resolution,[],[f690,f443])).
% 2.10/0.66  fof(f443,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))),
% 2.10/0.66    inference(subsumption_resolution,[],[f442,f52])).
% 2.10/0.66  fof(f52,plain,(
% 2.10/0.66    ~v2_struct_0(sK0)),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f442,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f441,f53])).
% 2.10/0.66  fof(f53,plain,(
% 2.10/0.66    v2_pre_topc(sK0)),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f441,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f440,f54])).
% 2.10/0.66  fof(f54,plain,(
% 2.10/0.66    l1_pre_topc(sK0)),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f440,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f439,f55])).
% 2.10/0.66  fof(f55,plain,(
% 2.10/0.66    ~v2_struct_0(sK1)),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f439,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f438,f56])).
% 2.10/0.66  fof(f56,plain,(
% 2.10/0.66    m1_pre_topc(sK1,sK0)),
% 2.10/0.66    inference(cnf_transformation,[],[f48])).
% 2.10/0.66  fof(f438,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f437,f57])).
% 2.10/0.66  fof(f437,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f436,f58])).
% 2.10/0.66  fof(f436,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f435,f59])).
% 2.10/0.66  fof(f435,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(duplicate_literal_removal,[],[f432])).
% 2.10/0.66  fof(f432,plain,(
% 2.10/0.66    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.66    inference(superposition,[],[f66,f427])).
% 2.10/0.66  fof(f427,plain,(
% 2.10/0.66    k2_tmap_1(sK1,sK0,sK2,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)),
% 2.10/0.66    inference(forward_demodulation,[],[f426,f218])).
% 2.10/0.66  fof(f218,plain,(
% 2.10/0.66    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))),
% 2.10/0.66    inference(subsumption_resolution,[],[f217,f98])).
% 2.10/0.66  fof(f98,plain,(
% 2.10/0.66    l1_pre_topc(sK1)),
% 2.10/0.66    inference(subsumption_resolution,[],[f89,f54])).
% 2.10/0.66  fof(f89,plain,(
% 2.10/0.66    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.10/0.66    inference(resolution,[],[f56,f63])).
% 2.10/0.66  fof(f63,plain,(
% 2.10/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f20])).
% 2.10/0.66  fof(f20,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.10/0.66    inference(ennf_transformation,[],[f3])).
% 2.10/0.66  fof(f3,axiom,(
% 2.10/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.10/0.66  fof(f217,plain,(
% 2.10/0.66    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 2.10/0.66    inference(resolution,[],[f123,f62])).
% 2.10/0.66  fof(f62,plain,(
% 2.10/0.66    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f19])).
% 2.10/0.66  fof(f19,plain,(
% 2.10/0.66    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.10/0.66    inference(ennf_transformation,[],[f9])).
% 2.10/0.66  fof(f9,axiom,(
% 2.10/0.66    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.10/0.66  fof(f123,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f122,f55])).
% 2.10/0.66  fof(f122,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f121,f97])).
% 2.10/0.66  fof(f97,plain,(
% 2.10/0.66    v2_pre_topc(sK1)),
% 2.10/0.66    inference(subsumption_resolution,[],[f96,f53])).
% 2.10/0.66  fof(f96,plain,(
% 2.10/0.66    v2_pre_topc(sK1) | ~v2_pre_topc(sK0)),
% 2.10/0.66    inference(subsumption_resolution,[],[f88,f54])).
% 2.10/0.66  fof(f88,plain,(
% 2.10/0.66    v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.10/0.66    inference(resolution,[],[f56,f73])).
% 2.10/0.66  fof(f73,plain,(
% 2.10/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f36])).
% 2.10/0.66  fof(f36,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.10/0.66    inference(flattening,[],[f35])).
% 2.10/0.66  fof(f35,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f2])).
% 2.10/0.66  fof(f2,axiom,(
% 2.10/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.10/0.66  fof(f121,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f120,f98])).
% 2.10/0.66  fof(f120,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f119,f52])).
% 2.10/0.66  fof(f119,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f118,f53])).
% 2.10/0.66  fof(f118,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f117,f54])).
% 2.10/0.66  fof(f117,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f116,f57])).
% 2.10/0.66  fof(f116,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f101,f58])).
% 2.10/0.66  fof(f101,plain,(
% 2.10/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.10/0.66    inference(resolution,[],[f59,f70])).
% 2.10/0.66  fof(f70,plain,(
% 2.10/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f30])).
% 2.10/0.66  fof(f30,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.66    inference(flattening,[],[f29])).
% 2.10/0.66  fof(f29,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f5])).
% 2.10/0.66  fof(f5,axiom,(
% 2.10/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.10/0.66  fof(f426,plain,(
% 2.10/0.66    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)),
% 2.10/0.66    inference(subsumption_resolution,[],[f425,f98])).
% 2.10/0.66  fof(f425,plain,(
% 2.10/0.66    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) | ~l1_pre_topc(sK1)),
% 2.10/0.66    inference(resolution,[],[f341,f62])).
% 2.10/0.66  fof(f341,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f340,f52])).
% 2.10/0.66  fof(f340,plain,(
% 2.10/0.66    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f339,f53])).
% 2.10/0.66  fof(f339,plain,(
% 2.10/0.66    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) | ~m1_pre_topc(X0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f336,f54])).
% 2.10/0.66  fof(f336,plain,(
% 2.10/0.66    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(resolution,[],[f136,f56])).
% 2.10/0.66  fof(f136,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(sK1,X9) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~m1_pre_topc(X8,sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f135,f74])).
% 2.10/0.66  fof(f74,plain,(
% 2.10/0.66    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f38])).
% 2.10/0.66  fof(f38,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.10/0.66    inference(flattening,[],[f37])).
% 2.10/0.66  fof(f37,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f13])).
% 2.10/0.66  fof(f13,axiom,(
% 2.10/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.10/0.66  fof(f135,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(X8,sK1) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(sK1,X9) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f134,f52])).
% 2.10/0.66  fof(f134,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(X8,sK1) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(sK1,X9) | v2_struct_0(sK0) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f133,f53])).
% 2.10/0.66  fof(f133,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(X8,sK1) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(sK1,X9) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f132,f54])).
% 2.10/0.66  fof(f132,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(X8,sK1) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(sK1,X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f131,f57])).
% 2.10/0.66  fof(f131,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(X8,sK1) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(sK1,X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f103,f58])).
% 2.10/0.66  fof(f103,plain,(
% 2.10/0.66    ( ! [X8,X9] : (~m1_pre_topc(X8,sK1) | k3_tmap_1(X9,sK0,sK1,X8,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X8)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(sK1,X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 2.10/0.66    inference(resolution,[],[f59,f64])).
% 2.10/0.66  fof(f64,plain,(
% 2.10/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f22])).
% 2.10/0.66  fof(f22,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.66    inference(flattening,[],[f21])).
% 2.10/0.66  fof(f21,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f6])).
% 2.10/0.66  fof(f6,axiom,(
% 2.10/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.10/0.66  fof(f66,plain,(
% 2.10/0.66    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f26])).
% 2.10/0.66  fof(f26,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.66    inference(flattening,[],[f25])).
% 2.10/0.66  fof(f25,plain,(
% 2.10/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f12])).
% 2.10/0.66  fof(f12,axiom,(
% 2.10/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.10/0.66  fof(f690,plain,(
% 2.10/0.66    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k2_tmap_1(sK1,sK0,sK2,sK1)) | k2_tmap_1(sK1,sK0,sK2,sK1) = X10 | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X10)) ) | ~spl4_9),
% 2.10/0.66    inference(subsumption_resolution,[],[f689,f431])).
% 2.10/0.66  fof(f431,plain,(
% 2.10/0.66    v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))),
% 2.10/0.66    inference(backward_demodulation,[],[f229,f427])).
% 2.10/0.66  fof(f229,plain,(
% 2.10/0.66    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2))),
% 2.10/0.66    inference(resolution,[],[f224,f56])).
% 2.10/0.66  fof(f224,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f223,f52])).
% 2.10/0.66  fof(f223,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f222,f53])).
% 2.10/0.66  fof(f222,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f219,f54])).
% 2.10/0.66  fof(f219,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(resolution,[],[f110,f56])).
% 2.10/0.66  fof(f110,plain,(
% 2.10/0.66    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f109,f52])).
% 2.10/0.66  fof(f109,plain,(
% 2.10/0.66    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f108,f53])).
% 2.10/0.66  fof(f108,plain,(
% 2.10/0.66    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f107,f54])).
% 2.10/0.66  fof(f107,plain,(
% 2.10/0.66    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f106,f57])).
% 2.10/0.66  fof(f106,plain,(
% 2.10/0.66    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f99,f58])).
% 2.10/0.66  fof(f99,plain,(
% 2.10/0.66    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(resolution,[],[f59,f80])).
% 2.10/0.66  fof(f80,plain,(
% 2.10/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f44])).
% 2.10/0.66  fof(f44,plain,(
% 2.10/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.66    inference(flattening,[],[f43])).
% 2.10/0.66  fof(f43,plain,(
% 2.10/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.66    inference(ennf_transformation,[],[f7])).
% 2.10/0.66  fof(f7,axiom,(
% 2.10/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.10/0.66  fof(f689,plain,(
% 2.10/0.66    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k2_tmap_1(sK1,sK0,sK2,sK1)) | k2_tmap_1(sK1,sK0,sK2,sK1) = X10 | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X10)) ) | ~spl4_9),
% 2.10/0.66    inference(subsumption_resolution,[],[f656,f429])).
% 2.10/0.66  fof(f429,plain,(
% 2.10/0.66    v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_9),
% 2.10/0.66    inference(backward_demodulation,[],[f258,f427])).
% 2.10/0.66  fof(f258,plain,(
% 2.10/0.66    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_9),
% 2.10/0.66    inference(avatar_component_clause,[],[f257])).
% 2.10/0.66  fof(f257,plain,(
% 2.10/0.66    spl4_9 <=> v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.10/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.10/0.66  fof(f656,plain,(
% 2.10/0.66    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k2_tmap_1(sK1,sK0,sK2,sK1)) | k2_tmap_1(sK1,sK0,sK2,sK1) = X10 | ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X10)) )),
% 2.10/0.66    inference(resolution,[],[f430,f78])).
% 2.10/0.66  fof(f78,plain,(
% 2.10/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f51])).
% 2.10/0.66  fof(f51,plain,(
% 2.10/0.66    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.10/0.66    inference(nnf_transformation,[],[f42])).
% 2.10/0.66  fof(f42,plain,(
% 2.10/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.10/0.66    inference(flattening,[],[f41])).
% 2.10/0.66  fof(f41,plain,(
% 2.10/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.10/0.66    inference(ennf_transformation,[],[f1])).
% 2.10/0.66  fof(f1,axiom,(
% 2.10/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.10/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.10/0.66  fof(f430,plain,(
% 2.10/0.66    m1_subset_1(k2_tmap_1(sK1,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.10/0.66    inference(backward_demodulation,[],[f243,f427])).
% 2.10/0.66  fof(f243,plain,(
% 2.10/0.66    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.10/0.66    inference(resolution,[],[f236,f56])).
% 2.10/0.66  fof(f236,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f235,f52])).
% 2.10/0.66  fof(f235,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f234,f53])).
% 2.10/0.66  fof(f234,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f231,f54])).
% 2.10/0.66  fof(f231,plain,(
% 2.10/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.10/0.66    inference(resolution,[],[f115,f56])).
% 2.10/0.66  fof(f115,plain,(
% 2.10/0.66    ( ! [X2,X3] : (~m1_pre_topc(sK1,X2) | ~m1_pre_topc(X3,X2) | m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f114,f52])).
% 2.10/0.66  fof(f114,plain,(
% 2.10/0.66    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f113,f53])).
% 2.10/0.66  fof(f113,plain,(
% 2.10/0.66    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f112,f54])).
% 2.10/0.66  fof(f112,plain,(
% 2.10/0.66    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f111,f57])).
% 2.10/0.66  fof(f111,plain,(
% 2.10/0.66    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.10/0.66    inference(subsumption_resolution,[],[f100,f58])).
% 2.10/0.66  fof(f100,plain,(
% 2.10/0.66    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.10/0.66    inference(resolution,[],[f59,f82])).
% 2.10/0.66  fof(f82,plain,(
% 2.10/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.66    inference(cnf_transformation,[],[f44])).
% 2.10/0.66  fof(f1026,plain,(
% 2.10/0.66    k4_tmap_1(sK0,sK1) != k2_tmap_1(sK1,sK0,sK2,sK1) | spl4_69),
% 2.10/0.66    inference(avatar_component_clause,[],[f1025])).
% 2.10/0.66  fof(f1025,plain,(
% 2.10/0.66    spl4_69 <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 2.10/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.10/0.67  fof(f3477,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_186)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3476,f59])).
% 2.10/0.67  fof(f3476,plain,(
% 2.10/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_186)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3475,f58])).
% 2.10/0.67  fof(f3475,plain,(
% 2.10/0.67    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_186)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3474,f57])).
% 2.10/0.67  fof(f3474,plain,(
% 2.10/0.67    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_186)),
% 2.10/0.67    inference(resolution,[],[f3366,f203])).
% 2.10/0.67  fof(f203,plain,(
% 2.10/0.67    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = X10) ) | ~spl4_7),
% 2.10/0.67    inference(avatar_component_clause,[],[f202])).
% 2.10/0.67  fof(f202,plain,(
% 2.10/0.67    spl4_7 <=> ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = X10)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.10/0.67  fof(f3366,plain,(
% 2.10/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~spl4_186),
% 2.10/0.67    inference(avatar_component_clause,[],[f3364])).
% 2.10/0.67  fof(f3364,plain,(
% 2.10/0.67    spl4_186 <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).
% 2.10/0.67  fof(f3464,plain,(
% 2.10/0.67    ~spl4_68 | ~spl4_70 | spl4_185),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f3463])).
% 2.10/0.67  fof(f3463,plain,(
% 2.10/0.67    $false | (~spl4_68 | ~spl4_70 | spl4_185)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3462,f52])).
% 2.10/0.67  fof(f3462,plain,(
% 2.10/0.67    v2_struct_0(sK0) | (~spl4_68 | ~spl4_70 | spl4_185)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3461,f53])).
% 2.10/0.67  fof(f3461,plain,(
% 2.10/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_68 | ~spl4_70 | spl4_185)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3460,f54])).
% 2.10/0.67  fof(f3460,plain,(
% 2.10/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_68 | ~spl4_70 | spl4_185)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3456,f3362])).
% 2.10/0.67  fof(f3362,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | spl4_185),
% 2.10/0.67    inference(avatar_component_clause,[],[f3360])).
% 2.10/0.67  fof(f3360,plain,(
% 2.10/0.67    spl4_185 <=> sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_185])])).
% 2.10/0.67  fof(f3456,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(resolution,[],[f3452,f56])).
% 2.10/0.67  fof(f3452,plain,(
% 2.10/0.67    ( ! [X1] : (~m1_pre_topc(sK1,X1) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X1,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1202,f1030])).
% 2.10/0.67  fof(f1030,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_pre_topc(sK1,X0) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_68),
% 2.10/0.67    inference(subsumption_resolution,[],[f1029,f55])).
% 2.10/0.67  fof(f1029,plain,(
% 2.10/0.67    ( ! [X0] : (m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_68),
% 2.10/0.67    inference(resolution,[],[f1023,f72])).
% 2.10/0.67  fof(f72,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f34])).
% 2.10/0.67  fof(f34,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f33])).
% 2.10/0.67  fof(f33,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f4])).
% 2.10/0.67  fof(f4,axiom,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 2.10/0.67  fof(f1023,plain,(
% 2.10/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~spl4_68),
% 2.10/0.67    inference(avatar_component_clause,[],[f1021])).
% 2.10/0.67  fof(f1021,plain,(
% 2.10/0.67    spl4_68 <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 2.10/0.67  fof(f1202,plain,(
% 2.10/0.67    ( ! [X1] : (sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X1,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X1)) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl4_70),
% 2.10/0.67    inference(subsumption_resolution,[],[f1189,f55])).
% 2.10/0.67  fof(f1189,plain,(
% 2.10/0.67    ( ! [X1] : (sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X1,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X1)) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl4_70),
% 2.10/0.67    inference(resolution,[],[f1044,f71])).
% 2.10/0.67  fof(f71,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f32])).
% 2.10/0.67  fof(f32,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f31])).
% 2.10/0.67  fof(f31,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f14])).
% 2.10/0.67  fof(f14,axiom,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.10/0.67  fof(f1044,plain,(
% 2.10/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~spl4_70),
% 2.10/0.67    inference(avatar_component_clause,[],[f1042])).
% 2.10/0.67  fof(f1042,plain,(
% 2.10/0.67    spl4_70 <=> r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 2.10/0.67  fof(f3367,plain,(
% 2.10/0.67    ~spl4_185 | spl4_186 | ~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72),
% 2.10/0.67    inference(avatar_split_clause,[],[f3358,f1195,f1042,f1021,f468,f257,f155,f3364,f3360])).
% 2.10/0.67  fof(f155,plain,(
% 2.10/0.67    spl4_1 <=> v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.10/0.67  fof(f468,plain,(
% 2.10/0.67    spl4_27 <=> m1_pre_topc(sK1,sK1)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.10/0.67  fof(f1195,plain,(
% 2.10/0.67    spl4_72 <=> sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 2.10/0.67  fof(f3358,plain,(
% 2.10/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(forward_demodulation,[],[f3357,f2105])).
% 2.10/0.67  fof(f3357,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3356,f52])).
% 2.10/0.67  fof(f3356,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3355,f53])).
% 2.10/0.67  fof(f3355,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3354,f54])).
% 2.10/0.67  fof(f3354,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3353,f97])).
% 2.10/0.67  fof(f3353,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3352,f98])).
% 2.10/0.67  fof(f3352,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3351,f55])).
% 2.10/0.67  fof(f3351,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3350,f469])).
% 2.10/0.67  fof(f469,plain,(
% 2.10/0.67    m1_pre_topc(sK1,sK1) | ~spl4_27),
% 2.10/0.67    inference(avatar_component_clause,[],[f468])).
% 2.10/0.67  fof(f3350,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3349,f57])).
% 2.10/0.67  fof(f3349,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3348,f58])).
% 2.10/0.67  fof(f3348,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3347,f59])).
% 2.10/0.67  fof(f3347,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3346,f92])).
% 2.10/0.67  fof(f92,plain,(
% 2.10/0.67    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.10/0.67    inference(subsumption_resolution,[],[f91,f52])).
% 2.10/0.67  fof(f91,plain,(
% 2.10/0.67    v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 2.10/0.67    inference(subsumption_resolution,[],[f90,f53])).
% 2.10/0.67  fof(f90,plain,(
% 2.10/0.67    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.67    inference(subsumption_resolution,[],[f85,f54])).
% 2.10/0.67  fof(f85,plain,(
% 2.10/0.67    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.67    inference(resolution,[],[f56,f75])).
% 2.10/0.67  fof(f75,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k4_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f40])).
% 2.10/0.67  fof(f40,plain,(
% 2.10/0.67    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f39])).
% 2.10/0.67  fof(f39,plain,(
% 2.10/0.67    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f8])).
% 2.10/0.67  fof(f8,axiom,(
% 2.10/0.67    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.10/0.67  fof(f3346,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3345,f156])).
% 2.10/0.67  fof(f156,plain,(
% 2.10/0.67    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_1),
% 2.10/0.67    inference(avatar_component_clause,[],[f155])).
% 2.10/0.67  fof(f3345,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3344,f95])).
% 2.10/0.67  fof(f95,plain,(
% 2.10/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.10/0.67    inference(subsumption_resolution,[],[f94,f52])).
% 2.10/0.67  fof(f94,plain,(
% 2.10/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0)),
% 2.10/0.67    inference(subsumption_resolution,[],[f93,f53])).
% 2.10/0.67  fof(f93,plain,(
% 2.10/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.67    inference(subsumption_resolution,[],[f86,f54])).
% 2.10/0.67  fof(f86,plain,(
% 2.10/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.10/0.67    inference(resolution,[],[f56,f77])).
% 2.10/0.67  fof(f77,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f40])).
% 2.10/0.67  fof(f3344,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(duplicate_literal_removal,[],[f3343])).
% 2.10/0.67  fof(f3343,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(superposition,[],[f69,f3031])).
% 2.10/0.67  fof(f3031,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70 | ~spl4_72)),
% 2.10/0.67    inference(forward_demodulation,[],[f3030,f1197])).
% 2.10/0.67  fof(f1197,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~spl4_72),
% 2.10/0.67    inference(avatar_component_clause,[],[f1195])).
% 2.10/0.67  fof(f3030,plain,(
% 2.10/0.67    k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_9 | ~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(forward_demodulation,[],[f3029,f2121])).
% 2.10/0.67  fof(f2121,plain,(
% 2.10/0.67    sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) | ~spl4_9),
% 2.10/0.67    inference(backward_demodulation,[],[f427,f2105])).
% 2.10/0.67  fof(f3029,plain,(
% 2.10/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3028,f52])).
% 2.10/0.67  fof(f3028,plain,(
% 2.10/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | v2_struct_0(sK0) | (~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3027,f53])).
% 2.10/0.67  fof(f3027,plain,(
% 2.10/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f3023,f54])).
% 2.10/0.67  fof(f3023,plain,(
% 2.10/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(resolution,[],[f1201,f56])).
% 2.10/0.67  fof(f1201,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_pre_topc(sK1,X0) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1200,f55])).
% 2.10/0.67  fof(f1200,plain,(
% 2.10/0.67    ( ! [X0] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl4_27 | ~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1199,f469])).
% 2.10/0.67  fof(f1199,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_pre_topc(sK1,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl4_68 | ~spl4_70)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1188,f1023])).
% 2.10/0.67  fof(f1188,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k3_tmap_1(X0,sK0,sK1,sK1,sK2),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_70),
% 2.10/0.67    inference(resolution,[],[f1044,f130])).
% 2.10/0.67  fof(f130,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~m1_pre_topc(sK1,X7) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f129,f74])).
% 2.10/0.67  fof(f129,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~m1_pre_topc(sK1,X7) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f128,f52])).
% 2.10/0.67  fof(f128,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~m1_pre_topc(sK1,X7) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | v2_struct_0(sK0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f127,f53])).
% 2.10/0.67  fof(f127,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~m1_pre_topc(sK1,X7) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f126,f54])).
% 2.10/0.67  fof(f126,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~m1_pre_topc(sK1,X7) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f125,f55])).
% 2.10/0.67  fof(f125,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~m1_pre_topc(sK1,X7) | v2_struct_0(sK1) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f124,f57])).
% 2.10/0.67  fof(f124,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,X7) | v2_struct_0(sK1) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(subsumption_resolution,[],[f102,f58])).
% 2.10/0.67  fof(f102,plain,(
% 2.10/0.67    ( ! [X6,X7,X5] : (~r2_hidden(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_pre_topc(X6,sK1) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X5) = k1_funct_1(k3_tmap_1(X7,sK0,sK1,X6,sK2),X5) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,X7) | v2_struct_0(sK1) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 2.10/0.67    inference(resolution,[],[f59,f65])).
% 2.10/0.67  fof(f65,plain,(
% 2.10/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f24])).
% 2.10/0.67  fof(f24,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f23])).
% 2.10/0.67  fof(f23,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f11])).
% 2.10/0.67  fof(f11,axiom,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).
% 2.10/0.67  fof(f69,plain,(
% 2.10/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f50])).
% 2.10/0.67  fof(f50,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f49])).
% 2.10/0.67  fof(f49,plain,(
% 2.10/0.67    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f28,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.67    inference(flattening,[],[f27])).
% 2.10/0.67  fof(f27,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f10])).
% 2.10/0.67  fof(f10,axiom,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.10/0.67  fof(f1582,plain,(
% 2.10/0.67    ~spl4_68 | spl4_71),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f1581])).
% 2.10/0.67  fof(f1581,plain,(
% 2.10/0.67    $false | (~spl4_68 | spl4_71)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1580,f52])).
% 2.10/0.67  fof(f1580,plain,(
% 2.10/0.67    v2_struct_0(sK0) | (~spl4_68 | spl4_71)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1579,f54])).
% 2.10/0.67  fof(f1579,plain,(
% 2.10/0.67    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_68 | spl4_71)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1575,f1193])).
% 2.10/0.67  fof(f1193,plain,(
% 2.10/0.67    ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | spl4_71),
% 2.10/0.67    inference(avatar_component_clause,[],[f1191])).
% 2.10/0.67  fof(f1191,plain,(
% 2.10/0.67    spl4_71 <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 2.10/0.67  fof(f1575,plain,(
% 2.10/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_68),
% 2.10/0.67    inference(resolution,[],[f1030,f56])).
% 2.10/0.67  fof(f1198,plain,(
% 2.10/0.67    ~spl4_71 | spl4_72 | ~spl4_70),
% 2.10/0.67    inference(avatar_split_clause,[],[f1187,f1042,f1195,f1191])).
% 2.10/0.67  fof(f1187,plain,(
% 2.10/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~spl4_70),
% 2.10/0.67    inference(resolution,[],[f1044,f60])).
% 2.10/0.67  fof(f60,plain,(
% 2.10/0.67    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f48])).
% 2.10/0.67  fof(f1121,plain,(
% 2.10/0.67    ~spl4_7 | ~spl4_69),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f1120])).
% 2.10/0.67  fof(f1120,plain,(
% 2.10/0.67    $false | (~spl4_7 | ~spl4_69)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1085,f140])).
% 2.10/0.67  fof(f140,plain,(
% 2.10/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 2.10/0.67    inference(subsumption_resolution,[],[f139,f57])).
% 2.10/0.67  fof(f139,plain,(
% 2.10/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | ~v1_funct_1(sK2)),
% 2.10/0.67    inference(subsumption_resolution,[],[f105,f58])).
% 2.10/0.67  fof(f105,plain,(
% 2.10/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 2.10/0.67    inference(resolution,[],[f59,f84])).
% 2.10/0.67  fof(f84,plain,(
% 2.10/0.67    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.10/0.67    inference(duplicate_literal_removal,[],[f83])).
% 2.10/0.67  fof(f83,plain,(
% 2.10/0.67    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.10/0.67    inference(equality_resolution,[],[f79])).
% 2.10/0.67  fof(f79,plain,(
% 2.10/0.67    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f51])).
% 2.10/0.67  fof(f1085,plain,(
% 2.10/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | (~spl4_7 | ~spl4_69)),
% 2.10/0.67    inference(backward_demodulation,[],[f61,f1084])).
% 2.10/0.67  fof(f1084,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_69)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1083,f59])).
% 2.10/0.67  fof(f1083,plain,(
% 2.10/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_69)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1082,f58])).
% 2.10/0.67  fof(f1082,plain,(
% 2.10/0.67    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_69)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1081,f57])).
% 2.10/0.67  fof(f1081,plain,(
% 2.10/0.67    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_7 | ~spl4_69)),
% 2.10/0.67    inference(resolution,[],[f1052,f203])).
% 2.10/0.67  fof(f1052,plain,(
% 2.10/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~spl4_69),
% 2.10/0.67    inference(backward_demodulation,[],[f443,f1027])).
% 2.10/0.67  fof(f1027,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | ~spl4_69),
% 2.10/0.67    inference(avatar_component_clause,[],[f1025])).
% 2.10/0.67  fof(f61,plain,(
% 2.10/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.10/0.67    inference(cnf_transformation,[],[f48])).
% 2.10/0.67  fof(f1045,plain,(
% 2.10/0.67    spl4_70 | spl4_69 | ~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27),
% 2.10/0.67    inference(avatar_split_clause,[],[f1040,f468,f257,f202,f155,f1025,f1042])).
% 2.10/0.67  fof(f1040,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1039,f55])).
% 2.10/0.67  fof(f1039,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1038,f97])).
% 2.10/0.67  fof(f1038,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1037,f98])).
% 2.10/0.67  fof(f1037,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1036,f469])).
% 2.10/0.67  fof(f1036,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1035,f57])).
% 2.10/0.67  fof(f1035,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1034,f58])).
% 2.10/0.67  fof(f1034,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1033,f59])).
% 2.10/0.67  fof(f1033,plain,(
% 2.10/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1032,f431])).
% 2.10/0.67  fof(f1032,plain,(
% 2.10/0.67    ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.67    inference(subsumption_resolution,[],[f1031,f429])).
% 2.10/0.67  fof(f1031,plain,(
% 2.10/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(resolution,[],[f649,f430])).
% 2.10/0.67  fof(f649,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(subsumption_resolution,[],[f648,f52])).
% 2.10/0.67  fof(f648,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(subsumption_resolution,[],[f647,f53])).
% 2.10/0.67  fof(f647,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(subsumption_resolution,[],[f646,f54])).
% 2.10/0.67  fof(f646,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(subsumption_resolution,[],[f645,f55])).
% 2.10/0.67  fof(f645,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(subsumption_resolution,[],[f644,f92])).
% 2.10/0.67  fof(f644,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.67    inference(subsumption_resolution,[],[f643,f156])).
% 2.10/0.67  fof(f643,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_7),
% 2.10/0.67    inference(subsumption_resolution,[],[f635,f95])).
% 2.10/0.67  fof(f635,plain,(
% 2.10/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_7),
% 2.10/0.67    inference(resolution,[],[f203,f68])).
% 2.10/0.68  fof(f68,plain,(
% 2.10/0.68    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f50])).
% 2.10/0.68  fof(f1028,plain,(
% 2.10/0.68    spl4_68 | spl4_69 | ~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27),
% 2.10/0.68    inference(avatar_split_clause,[],[f1019,f468,f257,f202,f155,f1025,f1021])).
% 2.10/0.68  fof(f1019,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1018,f55])).
% 2.10/0.68  fof(f1018,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1017,f97])).
% 2.10/0.68  fof(f1017,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1016,f98])).
% 2.10/0.68  fof(f1016,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1015,f469])).
% 2.10/0.68  fof(f1015,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1014,f57])).
% 2.10/0.68  fof(f1014,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1013,f58])).
% 2.10/0.68  fof(f1013,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1012,f59])).
% 2.10/0.68  fof(f1012,plain,(
% 2.10/0.68    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1011,f431])).
% 2.10/0.68  fof(f1011,plain,(
% 2.10/0.68    ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1010,f429])).
% 2.10/0.68  fof(f1010,plain,(
% 2.10/0.68    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(resolution,[],[f642,f430])).
% 2.10/0.68  fof(f642,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(subsumption_resolution,[],[f641,f52])).
% 2.10/0.68  fof(f641,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(subsumption_resolution,[],[f640,f53])).
% 2.10/0.68  fof(f640,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(subsumption_resolution,[],[f639,f54])).
% 2.10/0.68  fof(f639,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(subsumption_resolution,[],[f638,f55])).
% 2.10/0.68  fof(f638,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(subsumption_resolution,[],[f637,f92])).
% 2.10/0.68  fof(f637,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_1 | ~spl4_7)),
% 2.10/0.68    inference(subsumption_resolution,[],[f636,f156])).
% 2.10/0.68  fof(f636,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_7),
% 2.10/0.68    inference(subsumption_resolution,[],[f634,f95])).
% 2.10/0.68  fof(f634,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_7),
% 2.10/0.68    inference(resolution,[],[f203,f67])).
% 2.10/0.68  fof(f67,plain,(
% 2.10/0.68    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f50])).
% 2.10/0.68  fof(f492,plain,(
% 2.10/0.68    spl4_27),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f491])).
% 2.10/0.68  fof(f491,plain,(
% 2.10/0.68    $false | spl4_27),
% 2.10/0.68    inference(subsumption_resolution,[],[f490,f98])).
% 2.10/0.68  fof(f490,plain,(
% 2.10/0.68    ~l1_pre_topc(sK1) | spl4_27),
% 2.10/0.68    inference(resolution,[],[f470,f62])).
% 2.10/0.68  fof(f470,plain,(
% 2.10/0.68    ~m1_pre_topc(sK1,sK1) | spl4_27),
% 2.10/0.68    inference(avatar_component_clause,[],[f468])).
% 2.10/0.68  fof(f335,plain,(
% 2.10/0.68    spl4_9),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f334])).
% 2.10/0.68  fof(f334,plain,(
% 2.10/0.68    $false | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f333,f52])).
% 2.10/0.68  fof(f333,plain,(
% 2.10/0.68    v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f332,f53])).
% 2.10/0.68  fof(f332,plain,(
% 2.10/0.68    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f331,f54])).
% 2.10/0.68  fof(f331,plain,(
% 2.10/0.68    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f330,f56])).
% 2.10/0.68  fof(f330,plain,(
% 2.10/0.68    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f329,f57])).
% 2.10/0.68  fof(f329,plain,(
% 2.10/0.68    ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f328,f58])).
% 2.10/0.68  fof(f328,plain,(
% 2.10/0.68    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(subsumption_resolution,[],[f327,f59])).
% 2.10/0.68  fof(f327,plain,(
% 2.10/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f326])).
% 2.10/0.68  fof(f326,plain,(
% 2.10/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_9),
% 2.10/0.68    inference(resolution,[],[f259,f81])).
% 2.10/0.68  fof(f81,plain,(
% 2.10/0.68    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f44])).
% 2.10/0.68  fof(f259,plain,(
% 2.10/0.68    ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_9),
% 2.10/0.68    inference(avatar_component_clause,[],[f257])).
% 2.10/0.68  fof(f216,plain,(
% 2.10/0.68    spl4_1),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f215])).
% 2.10/0.68  fof(f215,plain,(
% 2.10/0.68    $false | spl4_1),
% 2.10/0.68    inference(subsumption_resolution,[],[f214,f52])).
% 2.10/0.68  fof(f214,plain,(
% 2.10/0.68    v2_struct_0(sK0) | spl4_1),
% 2.10/0.68    inference(subsumption_resolution,[],[f213,f53])).
% 2.10/0.68  fof(f213,plain,(
% 2.10/0.68    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_1),
% 2.10/0.68    inference(subsumption_resolution,[],[f212,f54])).
% 2.10/0.68  fof(f212,plain,(
% 2.10/0.68    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_1),
% 2.10/0.68    inference(subsumption_resolution,[],[f211,f56])).
% 2.10/0.68  fof(f211,plain,(
% 2.10/0.68    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_1),
% 2.10/0.68    inference(resolution,[],[f157,f76])).
% 2.10/0.68  fof(f76,plain,(
% 2.10/0.68    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f40])).
% 2.10/0.68  fof(f157,plain,(
% 2.10/0.68    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_1),
% 2.10/0.68    inference(avatar_component_clause,[],[f155])).
% 2.10/0.68  fof(f204,plain,(
% 2.10/0.68    ~spl4_1 | spl4_7),
% 2.10/0.68    inference(avatar_split_clause,[],[f200,f202,f155])).
% 2.10/0.68  fof(f200,plain,(
% 2.10/0.68    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = X10 | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X10)) )),
% 2.10/0.68    inference(subsumption_resolution,[],[f148,f92])).
% 2.10/0.68  fof(f148,plain,(
% 2.10/0.68    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X10,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = X10 | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X10,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X10)) )),
% 2.10/0.68    inference(resolution,[],[f95,f78])).
% 2.10/0.68  % SZS output end Proof for theBenchmark
% 2.10/0.68  % (10289)------------------------------
% 2.10/0.68  % (10289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.68  % (10289)Termination reason: Refutation
% 2.10/0.68  
% 2.10/0.68  % (10289)Memory used [KB]: 12153
% 2.10/0.68  % (10289)Time elapsed: 0.247 s
% 2.10/0.68  % (10289)------------------------------
% 2.10/0.68  % (10289)------------------------------
% 2.10/0.68  % (10286)Success in time 0.323 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:18 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  376 (6296 expanded)
%              Number of leaves         :   38 (2396 expanded)
%              Depth                    :   38
%              Number of atoms          : 2478 (70972 expanded)
%              Number of equality atoms :  161 (6522 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f187,f244,f267,f321,f384,f538,f552,f555,f1130,f1192,f1216,f1296,f1787,f1919,f3274,f3284])).

fof(f3284,plain,
    ( ~ spl4_12
    | ~ spl4_18
    | spl4_83
    | ~ spl4_92 ),
    inference(avatar_contradiction_clause,[],[f3283])).

fof(f3283,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_18
    | spl4_83
    | ~ spl4_92 ),
    inference(subsumption_resolution,[],[f3282,f1809])).

fof(f1809,plain,
    ( k4_tmap_1(sK0,sK1) != sK2
    | ~ spl4_18
    | spl4_83 ),
    inference(backward_demodulation,[],[f1124,f607])).

fof(f607,plain,
    ( sK2 = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f490,f320])).

fof(f320,plain,
    ( sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl4_18
  <=> sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f490,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) ),
    inference(forward_demodulation,[],[f489,f269])).

fof(f269,plain,(
    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f268,f115])).

fof(f115,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f105,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f57,f56,f55])).

fof(f55,plain,
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

fof(f56,plain,
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

fof(f57,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f105,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f66,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f268,plain,
    ( k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f154,f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f154,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f153,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f153,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f152,f113])).

fof(f113,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f112,f63])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,
    ( v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f103,f64])).

fof(f103,plain,
    ( v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f66,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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

fof(f152,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f151,f115])).

fof(f151,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f150,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f150,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f64])).

fof(f148,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f147,f67])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f147,plain,(
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
    inference(subsumption_resolution,[],[f130,f68])).

fof(f68,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f130,plain,(
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
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f489,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) ),
    inference(subsumption_resolution,[],[f488,f115])).

fof(f488,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f390,f73])).

fof(f390,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f389,f62])).

fof(f389,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f388,f63])).

fof(f388,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f385,f64])).

fof(f385,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f160,f66])).

fof(f160,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(sK1,X6)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f159,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f159,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f158,f62])).

fof(f158,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK1,X6)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f157,f63])).

fof(f157,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f156,f64])).

fof(f156,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f155,f67])).

fof(f155,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f131,f68])).

fof(f131,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK1)
      | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f69,f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f1124,plain,
    ( k4_tmap_1(sK0,sK1) != k2_tmap_1(sK1,sK0,sK2,sK1)
    | spl4_83 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1123,plain,
    ( spl4_83
  <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f3282,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_92 ),
    inference(subsumption_resolution,[],[f3281,f69])).

fof(f3281,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_92 ),
    inference(subsumption_resolution,[],[f3280,f68])).

fof(f3280,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_92 ),
    inference(subsumption_resolution,[],[f3279,f67])).

fof(f3279,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_92 ),
    inference(resolution,[],[f1918,f243])).

fof(f243,plain,
    ( ! [X7] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = X7 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_12
  <=> ! [X7] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | k4_tmap_1(sK0,sK1) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1918,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f1916])).

fof(f1916,plain,
    ( spl4_92
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f3274,plain,
    ( ~ spl4_87
    | spl4_91 ),
    inference(avatar_contradiction_clause,[],[f3273])).

fof(f3273,plain,
    ( $false
    | ~ spl4_87
    | spl4_91 ),
    inference(subsumption_resolution,[],[f3272,f62])).

fof(f3272,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_87
    | spl4_91 ),
    inference(subsumption_resolution,[],[f3271,f63])).

fof(f3271,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_87
    | spl4_91 ),
    inference(subsumption_resolution,[],[f3270,f64])).

fof(f3270,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_87
    | spl4_91 ),
    inference(subsumption_resolution,[],[f3269,f66])).

fof(f3269,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_87
    | spl4_91 ),
    inference(subsumption_resolution,[],[f3264,f1914])).

fof(f1914,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | spl4_91 ),
    inference(avatar_component_clause,[],[f1912])).

fof(f1912,plain,
    ( spl4_91
  <=> sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f3264,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_87 ),
    inference(resolution,[],[f1358,f1356])).

fof(f1356,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_87 ),
    inference(resolution,[],[f1215,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f114,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f114,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f104,f64])).

fof(f104,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f1215,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f1213,plain,
    ( spl4_87
  <=> r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f1358,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1357,f65])).

fof(f1357,plain,
    ( ! [X0] :
        ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_87 ),
    inference(resolution,[],[f1215,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f1919,plain,
    ( ~ spl4_91
    | spl4_92
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1910,f1213,f1064,f531,f318,f205,f172,f1916,f1912])).

fof(f172,plain,
    ( spl4_4
  <=> ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f205,plain,
    ( spl4_7
  <=> v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f531,plain,
    ( spl4_37
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1064,plain,
    ( spl4_81
  <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1910,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f1909,f607])).

fof(f1909,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1908,f62])).

fof(f1908,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1907,f63])).

fof(f1907,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1906,f64])).

fof(f1906,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1905,f113])).

fof(f1905,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1904,f115])).

fof(f1904,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1903,f65])).

fof(f1903,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_37
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1902,f532])).

fof(f532,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f531])).

fof(f1902,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1901,f67])).

fof(f1901,plain,
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
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1900,f68])).

fof(f1900,plain,
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
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1899,f69])).

fof(f1899,plain,
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
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1898,f108])).

fof(f108,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f107,f62])).

fof(f107,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f63])).

fof(f106,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f64])).

fof(f100,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f66,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k4_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f1898,plain,
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
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1897,f206])).

fof(f206,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f205])).

fof(f1897,plain,
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
    | ~ spl4_4
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1896,f111])).

fof(f111,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f110,f62])).

fof(f110,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f63])).

fof(f109,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f64])).

fof(f101,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f66,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1896,plain,
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
    | ~ spl4_4
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(duplicate_literal_removal,[],[f1895])).

fof(f1895,plain,
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
    | ~ spl4_4
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(superposition,[],[f81,f1894])).

fof(f1894,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_81
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f1199,f1355])).

fof(f1355,plain,
    ( sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_87 ),
    inference(resolution,[],[f1215,f188])).

fof(f188,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(subsumption_resolution,[],[f70,f117])).

fof(f70,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1199,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_81 ),
    inference(resolution,[],[f1066,f173])).

fof(f173,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1066,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f59])).

fof(f59,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
        & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f1787,plain,
    ( ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f1786])).

fof(f1786,plain,
    ( $false
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1785,f62])).

fof(f1785,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1784,f63])).

fof(f1784,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1783,f64])).

fof(f1783,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1782,f113])).

fof(f1782,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1781,f115])).

fof(f1781,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1780,f65])).

fof(f1780,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1779,f532])).

fof(f1779,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1778,f67])).

fof(f1778,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1777,f68])).

fof(f1777,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1776,f69])).

fof(f1776,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1775,f491])).

fof(f491,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2)
    | spl4_17 ),
    inference(backward_demodulation,[],[f316,f490])).

fof(f316,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl4_17
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1775,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2)
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
    | ~ spl4_4
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f1774,f1079])).

fof(f1079,plain,
    ( sK3(sK0,sK1,sK1,sK2,sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2))
    | ~ spl4_39 ),
    inference(resolution,[],[f551,f188])).

fof(f551,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl4_39
  <=> r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1774,plain,
    ( sK3(sK0,sK1,sK1,sK2,sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2)
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
    | ~ spl4_4
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(duplicate_literal_removal,[],[f1773])).

fof(f1773,plain,
    ( sK3(sK0,sK1,sK1,sK2,sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
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
    | ~ spl4_4
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(superposition,[],[f81,f1772])).

fof(f1772,plain,
    ( sK3(sK0,sK1,sK1,sK2,sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,sK2))
    | ~ spl4_4
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f1075,f1079])).

fof(f1075,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2))
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(resolution,[],[f537,f173])).

fof(f537,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl4_38
  <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1296,plain,
    ( ~ spl4_12
    | ~ spl4_83 ),
    inference(avatar_contradiction_clause,[],[f1295])).

fof(f1295,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_83 ),
    inference(subsumption_resolution,[],[f1260,f164])).

fof(f164,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f163,f67])).

fof(f163,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f133,f68])).

fof(f133,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f69,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f1260,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ spl4_12
    | ~ spl4_83 ),
    inference(backward_demodulation,[],[f71,f1255])).

fof(f1255,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_83 ),
    inference(subsumption_resolution,[],[f1254,f69])).

fof(f1254,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_83 ),
    inference(subsumption_resolution,[],[f1253,f68])).

fof(f1253,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_83 ),
    inference(subsumption_resolution,[],[f1252,f67])).

fof(f1252,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = sK2
    | ~ spl4_12
    | ~ spl4_83 ),
    inference(resolution,[],[f1223,f243])).

fof(f1223,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))
    | ~ spl4_83 ),
    inference(backward_demodulation,[],[f506,f1125])).

fof(f1125,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f506,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f505,f62])).

fof(f505,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f504,f63])).

fof(f504,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f503,f64])).

fof(f503,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f502,f65])).

fof(f502,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f501,f66])).

fof(f501,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f500,f67])).

fof(f500,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f499,f68])).

fof(f499,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f498,f69])).

fof(f498,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f495])).

fof(f495,plain,
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
    inference(superposition,[],[f78,f490])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f71,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f1216,plain,
    ( spl4_87
    | spl4_83
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1211,f531,f310,f242,f205,f1123,f1213])).

fof(f310,plain,
    ( spl4_16
  <=> v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1211,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1210,f65])).

fof(f1210,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1209,f113])).

fof(f1209,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1208,f115])).

fof(f1208,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1207,f532])).

fof(f1207,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1206,f67])).

fof(f1206,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1205,f68])).

fof(f1205,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1204,f69])).

fof(f1204,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1203,f494])).

fof(f494,plain,(
    v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f280,f490])).

fof(f280,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2)) ),
    inference(resolution,[],[f275,f66])).

fof(f275,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f274,f62])).

fof(f274,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f273,f63])).

fof(f273,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f64])).

fof(f270,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f141,f66])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f140,f62])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f139,f63])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f138,f64])).

fof(f138,plain,(
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
    inference(subsumption_resolution,[],[f137,f67])).

fof(f137,plain,(
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
    inference(subsumption_resolution,[],[f128,f68])).

fof(f128,plain,(
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
    inference(resolution,[],[f69,f94])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f1203,plain,
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
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1202,f492])).

fof(f492,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f311,f490])).

fof(f311,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f310])).

fof(f1202,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f749,f493])).

fof(f493,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f296,f490])).

fof(f296,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f287,f66])).

fof(f287,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f286,f62])).

fof(f286,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f285,f63])).

fof(f285,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f282,f64])).

fof(f282,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f146,f66])).

fof(f146,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(sK1,X2)
      | ~ m1_pre_topc(X3,X2)
      | m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f145,f62])).

fof(f145,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f144,f63])).

fof(f144,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK1,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f143,f64])).

fof(f143,plain,(
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
    inference(subsumption_resolution,[],[f142,f67])).

fof(f142,plain,(
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
    inference(subsumption_resolution,[],[f129,f68])).

fof(f129,plain,(
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
    inference(resolution,[],[f69,f96])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f749,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f748,f62])).

fof(f748,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f747,f63])).

fof(f747,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f746,f64])).

fof(f746,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f745,f65])).

fof(f745,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f744,f108])).

fof(f744,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f743,f206])).

fof(f743,plain,
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
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f735,f111])).

fof(f735,plain,
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
    | ~ spl4_12 ),
    inference(resolution,[],[f243,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f1192,plain,
    ( ~ spl4_16
    | spl4_84 ),
    inference(avatar_contradiction_clause,[],[f1191])).

fof(f1191,plain,
    ( $false
    | ~ spl4_16
    | spl4_84 ),
    inference(subsumption_resolution,[],[f1129,f492])).

fof(f1129,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_84 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1127,plain,
    ( spl4_84
  <=> v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1130,plain,
    ( spl4_81
    | spl4_83
    | ~ spl4_84
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1121,f531,f242,f205,f1127,f1123,f1064])).

fof(f1121,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1120,f65])).

fof(f1120,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1119,f113])).

fof(f1119,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1118,f115])).

fof(f1118,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1117,f532])).

fof(f1117,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1116,f67])).

fof(f1116,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1115,f68])).

fof(f1115,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1114,f69])).

fof(f1114,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1103,f494])).

fof(f1103,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f493,f742])).

fof(f742,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f741,f62])).

fof(f741,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f740,f63])).

fof(f740,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f739,f64])).

fof(f739,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f738,f65])).

fof(f738,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f737,f108])).

fof(f737,plain,
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
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f736,f206])).

fof(f736,plain,
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
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f734,f111])).

fof(f734,plain,
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
    | ~ spl4_12 ),
    inference(resolution,[],[f243,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f555,plain,(
    spl4_37 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | spl4_37 ),
    inference(subsumption_resolution,[],[f553,f115])).

fof(f553,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_37 ),
    inference(resolution,[],[f533,f73])).

fof(f533,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f531])).

fof(f552,plain,
    ( ~ spl4_37
    | spl4_39
    | spl4_17 ),
    inference(avatar_split_clause,[],[f547,f314,f549,f531])).

fof(f547,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f546,f62])).

fof(f546,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f545,f63])).

fof(f545,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f544,f64])).

fof(f544,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f543,f113])).

fof(f543,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f542,f115])).

fof(f542,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f541,f65])).

fof(f541,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f540,f67])).

fof(f540,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f539,f68])).

fof(f539,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f519,f69])).

fof(f519,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
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
    | spl4_17 ),
    inference(duplicate_literal_removal,[],[f518])).

fof(f518,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
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
    | spl4_17 ),
    inference(resolution,[],[f491,f80])).

fof(f538,plain,
    ( ~ spl4_37
    | spl4_38
    | spl4_17 ),
    inference(avatar_split_clause,[],[f529,f314,f535,f531])).

fof(f529,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f528,f62])).

fof(f528,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f527,f63])).

fof(f527,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f526,f64])).

fof(f526,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f525,f113])).

fof(f525,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f524,f115])).

fof(f524,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f523,f65])).

fof(f523,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f522,f67])).

fof(f522,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f521,f68])).

fof(f521,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f520,f69])).

fof(f520,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
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
    | spl4_17 ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
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
    | spl4_17 ),
    inference(resolution,[],[f491,f79])).

fof(f384,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f382,f62])).

fof(f382,plain,
    ( v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f381,f63])).

fof(f381,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f380,f64])).

fof(f380,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f379,f66])).

fof(f379,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f378,f67])).

fof(f378,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f377,f68])).

fof(f377,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f376,f69])).

fof(f376,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(duplicate_literal_removal,[],[f375])).

fof(f375,plain,
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
    | spl4_16 ),
    inference(resolution,[],[f312,f95])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f312,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f310])).

fof(f321,plain,
    ( ~ spl4_16
    | ~ spl4_17
    | spl4_18 ),
    inference(avatar_split_clause,[],[f308,f318,f314,f310])).

fof(f308,plain,
    ( sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f298,f280])).

fof(f298,plain,
    ( sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2)) ),
    inference(resolution,[],[f296,f162])).

fof(f162,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | sK2 = X7
      | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,sK2)
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f161,f67])).

fof(f161,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,sK2)
      | sK2 = X7
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f132,f68])).

fof(f132,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,sK2)
      | sK2 = X7
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f69,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f267,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f265,f62])).

fof(f265,plain,
    ( v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f264,f63])).

fof(f264,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f263,f64])).

fof(f263,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f262,f66])).

fof(f262,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(resolution,[],[f207,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f207,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f205])).

fof(f244,plain,
    ( ~ spl4_7
    | spl4_12 ),
    inference(avatar_split_clause,[],[f240,f242,f205])).

fof(f240,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1))
      | k4_tmap_1(sK0,sK1) = X7
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f195,f108])).

fof(f195,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1))
      | k4_tmap_1(sK0,sK1) = X7
      | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f111,f92])).

fof(f187,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f185,f65])).

fof(f185,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f184,f116])).

fof(f116,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f184,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f170,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f170,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_3
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f174,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f166,f172,f168])).

fof(f166,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f165,f67])).

fof(f165,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f134,f68])).

fof(f134,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f69,f91])).

% (16203)Refutation not found, incomplete strategy% (16203)------------------------------
% (16203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16196)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (16197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (16198)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (16214)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (16207)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (16199)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (16205)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (16215)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (16218)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (16195)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16210)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (16209)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (16200)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (16211)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (16194)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (16202)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.20/0.52  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16201)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (16194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16194)Memory used [KB]: 10618
% 0.20/0.52  % (16194)Time elapsed: 0.103 s
% 0.20/0.52  % (16194)------------------------------
% 0.20/0.52  % (16194)------------------------------
% 0.20/0.52  % (16219)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (16212)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (16217)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (16213)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (16206)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (16220)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (16203)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (16204)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.55  % (16216)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.26/0.66  % (16195)Refutation found. Thanks to Tanya!
% 2.26/0.66  % SZS status Theorem for theBenchmark
% 2.26/0.66  % SZS output start Proof for theBenchmark
% 2.26/0.66  fof(f3285,plain,(
% 2.26/0.66    $false),
% 2.26/0.66    inference(avatar_sat_refutation,[],[f174,f187,f244,f267,f321,f384,f538,f552,f555,f1130,f1192,f1216,f1296,f1787,f1919,f3274,f3284])).
% 2.26/0.66  fof(f3284,plain,(
% 2.26/0.66    ~spl4_12 | ~spl4_18 | spl4_83 | ~spl4_92),
% 2.26/0.66    inference(avatar_contradiction_clause,[],[f3283])).
% 2.26/0.66  fof(f3283,plain,(
% 2.26/0.66    $false | (~spl4_12 | ~spl4_18 | spl4_83 | ~spl4_92)),
% 2.26/0.66    inference(subsumption_resolution,[],[f3282,f1809])).
% 2.26/0.66  fof(f1809,plain,(
% 2.26/0.66    k4_tmap_1(sK0,sK1) != sK2 | (~spl4_18 | spl4_83)),
% 2.26/0.66    inference(backward_demodulation,[],[f1124,f607])).
% 2.26/0.66  fof(f607,plain,(
% 2.26/0.66    sK2 = k2_tmap_1(sK1,sK0,sK2,sK1) | ~spl4_18),
% 2.26/0.66    inference(backward_demodulation,[],[f490,f320])).
% 2.26/0.66  fof(f320,plain,(
% 2.26/0.66    sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) | ~spl4_18),
% 2.26/0.66    inference(avatar_component_clause,[],[f318])).
% 2.26/0.66  fof(f318,plain,(
% 2.26/0.66    spl4_18 <=> sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)),
% 2.26/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.26/0.66  fof(f490,plain,(
% 2.26/0.66    k2_tmap_1(sK1,sK0,sK2,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)),
% 2.26/0.66    inference(forward_demodulation,[],[f489,f269])).
% 2.26/0.66  fof(f269,plain,(
% 2.26/0.66    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f268,f115])).
% 2.26/0.66  fof(f115,plain,(
% 2.26/0.66    l1_pre_topc(sK1)),
% 2.26/0.66    inference(subsumption_resolution,[],[f105,f64])).
% 2.26/0.66  fof(f64,plain,(
% 2.26/0.66    l1_pre_topc(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f58])).
% 2.26/0.66  fof(f58,plain,(
% 2.26/0.66    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.26/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f57,f56,f55])).
% 2.26/0.66  fof(f55,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f56,plain,(
% 2.26/0.66    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f57,plain,(
% 2.26/0.66    ? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f22,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f21])).
% 2.26/0.66  fof(f21,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f20])).
% 2.26/0.66  fof(f20,negated_conjecture,(
% 2.26/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.26/0.66    inference(negated_conjecture,[],[f19])).
% 2.26/0.66  fof(f19,conjecture,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.26/0.66  fof(f105,plain,(
% 2.26/0.66    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(resolution,[],[f66,f74])).
% 2.26/0.66  fof(f74,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f25])).
% 2.26/0.66  fof(f25,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f7])).
% 2.26/0.66  fof(f7,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.26/0.66  fof(f66,plain,(
% 2.26/0.66    m1_pre_topc(sK1,sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f58])).
% 2.26/0.66  fof(f268,plain,(
% 2.26/0.66    k2_tmap_1(sK1,sK0,sK2,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 2.26/0.66    inference(resolution,[],[f154,f73])).
% 2.26/0.66  fof(f73,plain,(
% 2.26/0.66    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f24])).
% 2.26/0.66  fof(f24,plain,(
% 2.26/0.66    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f14])).
% 2.26/0.66  fof(f14,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.26/0.66  fof(f154,plain,(
% 2.26/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4))) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f153,f65])).
% 2.26/0.66  fof(f65,plain,(
% 2.26/0.66    ~v2_struct_0(sK1)),
% 2.26/0.66    inference(cnf_transformation,[],[f58])).
% 2.26/0.66  fof(f153,plain,(
% 2.26/0.66    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | v2_struct_0(sK1)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f152,f113])).
% 2.26/0.66  fof(f113,plain,(
% 2.26/0.66    v2_pre_topc(sK1)),
% 2.26/0.66    inference(subsumption_resolution,[],[f112,f63])).
% 2.26/0.67  fof(f63,plain,(
% 2.26/0.67    v2_pre_topc(sK0)),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f112,plain,(
% 2.26/0.67    v2_pre_topc(sK1) | ~v2_pre_topc(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f103,f64])).
% 2.26/0.67  fof(f103,plain,(
% 2.26/0.67    v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.26/0.67    inference(resolution,[],[f66,f84])).
% 2.26/0.67  fof(f84,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f40])).
% 2.26/0.67  fof(f40,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/0.67    inference(flattening,[],[f39])).
% 2.26/0.67  fof(f39,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f5])).
% 2.26/0.67  fof(f5,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.26/0.67  fof(f152,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f151,f115])).
% 2.26/0.67  fof(f151,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f150,f62])).
% 2.26/0.67  fof(f62,plain,(
% 2.26/0.67    ~v2_struct_0(sK0)),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f150,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f149,f63])).
% 2.26/0.67  fof(f149,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f148,f64])).
% 2.26/0.67  fof(f148,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f147,f67])).
% 2.26/0.67  fof(f67,plain,(
% 2.26/0.67    v1_funct_1(sK2)),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f147,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f130,f68])).
% 2.26/0.67  fof(f68,plain,(
% 2.26/0.67    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f130,plain,(
% 2.26/0.67    ( ! [X4] : (~m1_pre_topc(X4,sK1) | k2_tmap_1(sK1,sK0,sK2,X4) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X4)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.26/0.67    inference(resolution,[],[f69,f82])).
% 2.26/0.67  fof(f82,plain,(
% 2.26/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f36])).
% 2.26/0.67  fof(f36,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f35])).
% 2.26/0.67  fof(f35,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f9])).
% 2.26/0.67  fof(f9,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.26/0.67  fof(f69,plain,(
% 2.26/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f489,plain,(
% 2.26/0.67    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2)),
% 2.26/0.67    inference(subsumption_resolution,[],[f488,f115])).
% 2.26/0.67  fof(f488,plain,(
% 2.26/0.67    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) | ~l1_pre_topc(sK1)),
% 2.26/0.67    inference(resolution,[],[f390,f73])).
% 2.26/0.67  fof(f390,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f389,f62])).
% 2.26/0.67  fof(f389,plain,(
% 2.26/0.67    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f388,f63])).
% 2.26/0.67  fof(f388,plain,(
% 2.26/0.67    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) | ~m1_pre_topc(X0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f385,f64])).
% 2.26/0.67  fof(f385,plain,(
% 2.26/0.67    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,sK2) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(resolution,[],[f160,f66])).
% 2.26/0.67  fof(f160,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(sK1,X6) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~m1_pre_topc(X5,sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f159,f85])).
% 2.26/0.67  fof(f85,plain,(
% 2.26/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f42])).
% 2.26/0.67  fof(f42,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/0.67    inference(flattening,[],[f41])).
% 2.26/0.67  fof(f41,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f17])).
% 2.26/0.67  fof(f17,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.26/0.67  fof(f159,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(X5,sK1) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK1,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f158,f62])).
% 2.26/0.67  fof(f158,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(X5,sK1) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK1,X6) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f157,f63])).
% 2.26/0.67  fof(f157,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(X5,sK1) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK1,X6) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f156,f64])).
% 2.26/0.67  fof(f156,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(X5,sK1) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK1,X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f155,f67])).
% 2.26/0.67  fof(f155,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(X5,sK1) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK1,X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f131,f68])).
% 2.26/0.67  fof(f131,plain,(
% 2.26/0.67    ( ! [X6,X5] : (~m1_pre_topc(X5,sK1) | k3_tmap_1(X6,sK0,sK1,X5,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,u1_struct_0(X5)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK1,X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.26/0.67    inference(resolution,[],[f69,f77])).
% 2.26/0.67  fof(f77,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f30])).
% 2.26/0.67  fof(f30,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f29])).
% 2.26/0.67  fof(f29,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f10])).
% 2.26/0.67  fof(f10,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.26/0.67  fof(f1124,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) != k2_tmap_1(sK1,sK0,sK2,sK1) | spl4_83),
% 2.26/0.67    inference(avatar_component_clause,[],[f1123])).
% 2.26/0.67  fof(f1123,plain,(
% 2.26/0.67    spl4_83 <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1)),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 2.26/0.67  fof(f3282,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_92)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3281,f69])).
% 2.26/0.67  fof(f3281,plain,(
% 2.26/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_92)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3280,f68])).
% 2.26/0.67  fof(f3280,plain,(
% 2.26/0.67    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_92)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3279,f67])).
% 2.26/0.67  fof(f3279,plain,(
% 2.26/0.67    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_92)),
% 2.26/0.67    inference(resolution,[],[f1918,f243])).
% 2.26/0.67  fof(f243,plain,(
% 2.26/0.67    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = X7) ) | ~spl4_12),
% 2.26/0.67    inference(avatar_component_clause,[],[f242])).
% 2.26/0.67  fof(f242,plain,(
% 2.26/0.67    spl4_12 <=> ! [X7] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = X7)),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.26/0.67  fof(f1918,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~spl4_92),
% 2.26/0.67    inference(avatar_component_clause,[],[f1916])).
% 2.26/0.67  fof(f1916,plain,(
% 2.26/0.67    spl4_92 <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 2.26/0.67  fof(f3274,plain,(
% 2.26/0.67    ~spl4_87 | spl4_91),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f3273])).
% 2.26/0.67  fof(f3273,plain,(
% 2.26/0.67    $false | (~spl4_87 | spl4_91)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3272,f62])).
% 2.26/0.67  fof(f3272,plain,(
% 2.26/0.67    v2_struct_0(sK0) | (~spl4_87 | spl4_91)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3271,f63])).
% 2.26/0.67  fof(f3271,plain,(
% 2.26/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_87 | spl4_91)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3270,f64])).
% 2.26/0.67  fof(f3270,plain,(
% 2.26/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_87 | spl4_91)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3269,f66])).
% 2.26/0.67  fof(f3269,plain,(
% 2.26/0.67    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_87 | spl4_91)),
% 2.26/0.67    inference(subsumption_resolution,[],[f3264,f1914])).
% 2.26/0.67  fof(f1914,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | spl4_91),
% 2.26/0.67    inference(avatar_component_clause,[],[f1912])).
% 2.26/0.67  fof(f1912,plain,(
% 2.26/0.67    spl4_91 <=> sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 2.26/0.67  fof(f3264,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_87),
% 2.26/0.67    inference(resolution,[],[f1358,f1356])).
% 2.26/0.67  fof(f1356,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | ~spl4_87),
% 2.26/0.67    inference(resolution,[],[f1215,f117])).
% 2.26/0.67  fof(f117,plain,(
% 2.26/0.67    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.26/0.67    inference(resolution,[],[f114,f90])).
% 2.26/0.67  fof(f90,plain,(
% 2.26/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f48])).
% 2.26/0.67  fof(f48,plain,(
% 2.26/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.26/0.67    inference(flattening,[],[f47])).
% 2.26/0.67  fof(f47,plain,(
% 2.26/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.26/0.67    inference(ennf_transformation,[],[f2])).
% 2.26/0.67  fof(f2,axiom,(
% 2.26/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.26/0.67  fof(f114,plain,(
% 2.26/0.67    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.67    inference(subsumption_resolution,[],[f104,f64])).
% 2.26/0.67  fof(f104,plain,(
% 2.26/0.67    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.26/0.67    inference(resolution,[],[f66,f75])).
% 2.26/0.67  fof(f75,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f26])).
% 2.26/0.67  fof(f26,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.67    inference(ennf_transformation,[],[f13])).
% 2.26/0.67  fof(f13,axiom,(
% 2.26/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.26/0.67  fof(f1215,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~spl4_87),
% 2.26/0.67    inference(avatar_component_clause,[],[f1213])).
% 2.26/0.67  fof(f1213,plain,(
% 2.26/0.67    spl4_87 <=> r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 2.26/0.67  fof(f1358,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_87),
% 2.26/0.67    inference(subsumption_resolution,[],[f1357,f65])).
% 2.26/0.67  fof(f1357,plain,(
% 2.26/0.67    ( ! [X0] : (sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(X0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_87),
% 2.26/0.67    inference(resolution,[],[f1215,f83])).
% 2.26/0.67  fof(f83,plain,(
% 2.26/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f38])).
% 2.26/0.67  fof(f38,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f37])).
% 2.26/0.67  fof(f37,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f18])).
% 2.26/0.67  fof(f18,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.26/0.67  fof(f1919,plain,(
% 2.26/0.67    ~spl4_91 | spl4_92 | ~spl4_4 | ~spl4_7 | ~spl4_18 | ~spl4_37 | ~spl4_81 | ~spl4_87),
% 2.26/0.67    inference(avatar_split_clause,[],[f1910,f1213,f1064,f531,f318,f205,f172,f1916,f1912])).
% 2.26/0.67  fof(f172,plain,(
% 2.26/0.67    spl4_4 <=> ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.26/0.67  fof(f205,plain,(
% 2.26/0.67    spl4_7 <=> v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.26/0.67  fof(f531,plain,(
% 2.26/0.67    spl4_37 <=> m1_pre_topc(sK1,sK1)),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.26/0.67  fof(f1064,plain,(
% 2.26/0.67    spl4_81 <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 2.26/0.67  fof(f1910,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_4 | ~spl4_7 | ~spl4_18 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(forward_demodulation,[],[f1909,f607])).
% 2.26/0.67  fof(f1909,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1908,f62])).
% 2.26/0.67  fof(f1908,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1907,f63])).
% 2.26/0.67  fof(f1907,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1906,f64])).
% 2.26/0.67  fof(f1906,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1905,f113])).
% 2.26/0.67  fof(f1905,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1904,f115])).
% 2.26/0.67  fof(f1904,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1903,f65])).
% 2.26/0.67  fof(f1903,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_37 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1902,f532])).
% 2.26/0.67  fof(f532,plain,(
% 2.26/0.67    m1_pre_topc(sK1,sK1) | ~spl4_37),
% 2.26/0.67    inference(avatar_component_clause,[],[f531])).
% 2.26/0.67  fof(f1902,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1901,f67])).
% 2.26/0.67  fof(f1901,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1900,f68])).
% 2.26/0.67  fof(f1900,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1899,f69])).
% 2.26/0.67  fof(f1899,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1898,f108])).
% 2.26/0.67  fof(f108,plain,(
% 2.26/0.67    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.26/0.67    inference(subsumption_resolution,[],[f107,f62])).
% 2.26/0.67  fof(f107,plain,(
% 2.26/0.67    v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f106,f63])).
% 2.26/0.67  fof(f106,plain,(
% 2.26/0.67    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f100,f64])).
% 2.26/0.67  fof(f100,plain,(
% 2.26/0.67    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(resolution,[],[f66,f87])).
% 2.26/0.67  fof(f87,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k4_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f46])).
% 2.26/0.67  fof(f46,plain,(
% 2.26/0.67    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f45])).
% 2.26/0.67  fof(f45,plain,(
% 2.26/0.67    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f12])).
% 2.26/0.67  fof(f12,axiom,(
% 2.26/0.67    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.26/0.67  fof(f1898,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1897,f206])).
% 2.26/0.67  fof(f206,plain,(
% 2.26/0.67    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_7),
% 2.26/0.67    inference(avatar_component_clause,[],[f205])).
% 2.26/0.67  fof(f1897,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1896,f111])).
% 2.26/0.67  fof(f111,plain,(
% 2.26/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.26/0.67    inference(subsumption_resolution,[],[f110,f62])).
% 2.26/0.67  fof(f110,plain,(
% 2.26/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f109,f63])).
% 2.26/0.67  fof(f109,plain,(
% 2.26/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f101,f64])).
% 2.26/0.67  fof(f101,plain,(
% 2.26/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(resolution,[],[f66,f89])).
% 2.26/0.67  fof(f89,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f46])).
% 2.26/0.67  fof(f1896,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f1895])).
% 2.26/0.67  fof(f1895,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(superposition,[],[f81,f1894])).
% 2.26/0.67  fof(f1894,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_4 | ~spl4_81 | ~spl4_87)),
% 2.26/0.67    inference(forward_demodulation,[],[f1199,f1355])).
% 2.26/0.67  fof(f1355,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | ~spl4_87),
% 2.26/0.67    inference(resolution,[],[f1215,f188])).
% 2.26/0.67  fof(f188,plain,(
% 2.26/0.67    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f70,f117])).
% 2.26/0.67  fof(f70,plain,(
% 2.26/0.67    ( ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f1199,plain,(
% 2.26/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1))) | (~spl4_4 | ~spl4_81)),
% 2.26/0.67    inference(resolution,[],[f1066,f173])).
% 2.26/0.67  fof(f173,plain,(
% 2.26/0.67    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8)) ) | ~spl4_4),
% 2.26/0.67    inference(avatar_component_clause,[],[f172])).
% 2.26/0.67  fof(f1066,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~spl4_81),
% 2.26/0.67    inference(avatar_component_clause,[],[f1064])).
% 2.26/0.67  fof(f81,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f60])).
% 2.26/0.67  fof(f60,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f59])).
% 2.26/0.67  fof(f59,plain,(
% 2.26/0.67    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 2.26/0.67    introduced(choice_axiom,[])).
% 2.26/0.67  fof(f34,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f33])).
% 2.26/0.67  fof(f33,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f15])).
% 2.26/0.67  fof(f15,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.26/0.67  fof(f1787,plain,(
% 2.26/0.67    ~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f1786])).
% 2.26/0.67  fof(f1786,plain,(
% 2.26/0.67    $false | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1785,f62])).
% 2.26/0.67  fof(f1785,plain,(
% 2.26/0.67    v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1784,f63])).
% 2.26/0.67  fof(f1784,plain,(
% 2.26/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1783,f64])).
% 2.26/0.67  fof(f1783,plain,(
% 2.26/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1782,f113])).
% 2.26/0.67  fof(f1782,plain,(
% 2.26/0.67    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1781,f115])).
% 2.26/0.67  fof(f1781,plain,(
% 2.26/0.67    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1780,f65])).
% 2.26/0.67  fof(f1780,plain,(
% 2.26/0.67    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_37 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1779,f532])).
% 2.26/0.67  fof(f1779,plain,(
% 2.26/0.67    ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1778,f67])).
% 2.26/0.67  fof(f1778,plain,(
% 2.26/0.67    ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1777,f68])).
% 2.26/0.67  fof(f1777,plain,(
% 2.26/0.67    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1776,f69])).
% 2.26/0.67  fof(f1776,plain,(
% 2.26/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_17 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1775,f491])).
% 2.26/0.67  fof(f491,plain,(
% 2.26/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2) | spl4_17),
% 2.26/0.67    inference(backward_demodulation,[],[f316,f490])).
% 2.26/0.67  fof(f316,plain,(
% 2.26/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2) | spl4_17),
% 2.26/0.67    inference(avatar_component_clause,[],[f314])).
% 2.26/0.67  fof(f314,plain,(
% 2.26/0.67    spl4_17 <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2)),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.26/0.67  fof(f1775,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1774,f1079])).
% 2.26/0.67  fof(f1079,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2)) | ~spl4_39),
% 2.26/0.67    inference(resolution,[],[f551,f188])).
% 2.26/0.67  fof(f551,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~spl4_39),
% 2.26/0.67    inference(avatar_component_clause,[],[f549])).
% 2.26/0.67  fof(f549,plain,(
% 2.26/0.67    spl4_39 <=> r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.26/0.67  fof(f1774,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f1773])).
% 2.26/0.67  fof(f1773,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK2,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(superposition,[],[f81,f1772])).
% 2.26/0.67  fof(f1772,plain,(
% 2.26/0.67    sK3(sK0,sK1,sK1,sK2,sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,sK2)) | (~spl4_4 | ~spl4_38 | ~spl4_39)),
% 2.26/0.67    inference(forward_demodulation,[],[f1075,f1079])).
% 2.26/0.67  fof(f1075,plain,(
% 2.26/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK0,sK1,sK1,sK2,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,sK2,sK2)) | (~spl4_4 | ~spl4_38)),
% 2.26/0.67    inference(resolution,[],[f537,f173])).
% 2.26/0.67  fof(f537,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~spl4_38),
% 2.26/0.67    inference(avatar_component_clause,[],[f535])).
% 2.26/0.67  fof(f535,plain,(
% 2.26/0.67    spl4_38 <=> m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 2.26/0.67  fof(f1296,plain,(
% 2.26/0.67    ~spl4_12 | ~spl4_83),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f1295])).
% 2.26/0.67  fof(f1295,plain,(
% 2.26/0.67    $false | (~spl4_12 | ~spl4_83)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1260,f164])).
% 2.26/0.67  fof(f164,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 2.26/0.67    inference(subsumption_resolution,[],[f163,f67])).
% 2.26/0.67  fof(f163,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | ~v1_funct_1(sK2)),
% 2.26/0.67    inference(subsumption_resolution,[],[f133,f68])).
% 2.26/0.67  fof(f133,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 2.26/0.67    inference(resolution,[],[f69,f98])).
% 2.26/0.67  fof(f98,plain,(
% 2.26/0.67    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f97])).
% 2.26/0.67  fof(f97,plain,(
% 2.26/0.67    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.26/0.67    inference(equality_resolution,[],[f93])).
% 2.26/0.67  fof(f93,plain,(
% 2.26/0.67    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f61])).
% 2.26/0.67  fof(f61,plain,(
% 2.26/0.67    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.26/0.67    inference(nnf_transformation,[],[f52])).
% 2.26/0.67  fof(f52,plain,(
% 2.26/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.26/0.67    inference(flattening,[],[f51])).
% 2.26/0.67  fof(f51,plain,(
% 2.26/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.26/0.67    inference(ennf_transformation,[],[f4])).
% 2.26/0.67  fof(f4,axiom,(
% 2.26/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.26/0.67  fof(f1260,plain,(
% 2.26/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | (~spl4_12 | ~spl4_83)),
% 2.26/0.67    inference(backward_demodulation,[],[f71,f1255])).
% 2.26/0.67  fof(f1255,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_83)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1254,f69])).
% 2.26/0.67  fof(f1254,plain,(
% 2.26/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_83)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1253,f68])).
% 2.26/0.67  fof(f1253,plain,(
% 2.26/0.67    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_83)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1252,f67])).
% 2.26/0.67  fof(f1252,plain,(
% 2.26/0.67    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = sK2 | (~spl4_12 | ~spl4_83)),
% 2.26/0.67    inference(resolution,[],[f1223,f243])).
% 2.26/0.67  fof(f1223,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k4_tmap_1(sK0,sK1)) | ~spl4_83),
% 2.26/0.67    inference(backward_demodulation,[],[f506,f1125])).
% 2.26/0.67  fof(f1125,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | ~spl4_83),
% 2.26/0.67    inference(avatar_component_clause,[],[f1123])).
% 2.26/0.67  fof(f506,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1))),
% 2.26/0.67    inference(subsumption_resolution,[],[f505,f62])).
% 2.26/0.67  fof(f505,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f504,f63])).
% 2.26/0.67  fof(f504,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f503,f64])).
% 2.26/0.67  fof(f503,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f502,f65])).
% 2.26/0.67  fof(f502,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f501,f66])).
% 2.26/0.67  fof(f501,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f500,f67])).
% 2.26/0.67  fof(f500,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f499,f68])).
% 2.26/0.67  fof(f499,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(subsumption_resolution,[],[f498,f69])).
% 2.26/0.67  fof(f498,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f495])).
% 2.26/0.67  fof(f495,plain,(
% 2.26/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tmap_1(sK1,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.26/0.67    inference(superposition,[],[f78,f490])).
% 2.26/0.67  fof(f78,plain,(
% 2.26/0.67    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f32])).
% 2.26/0.67  fof(f32,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f31])).
% 2.26/0.67  fof(f31,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f16])).
% 2.26/0.67  fof(f16,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.26/0.67  fof(f71,plain,(
% 2.26/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.26/0.67    inference(cnf_transformation,[],[f58])).
% 2.26/0.67  fof(f1216,plain,(
% 2.26/0.67    spl4_87 | spl4_83 | ~spl4_7 | ~spl4_12 | ~spl4_16 | ~spl4_37),
% 2.26/0.67    inference(avatar_split_clause,[],[f1211,f531,f310,f242,f205,f1123,f1213])).
% 2.26/0.67  fof(f310,plain,(
% 2.26/0.67    spl4_16 <=> v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.26/0.67  fof(f1211,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | (~spl4_7 | ~spl4_12 | ~spl4_16 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1210,f65])).
% 2.26/0.67  fof(f1210,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1209,f113])).
% 2.26/0.67  fof(f1209,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1208,f115])).
% 2.26/0.67  fof(f1208,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1207,f532])).
% 2.26/0.67  fof(f1207,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1206,f67])).
% 2.26/0.67  fof(f1206,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1205,f68])).
% 2.26/0.67  fof(f1205,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1204,f69])).
% 2.26/0.67  fof(f1204,plain,(
% 2.26/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1203,f494])).
% 2.26/0.67  fof(f494,plain,(
% 2.26/0.67    v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1))),
% 2.26/0.67    inference(backward_demodulation,[],[f280,f490])).
% 2.26/0.67  fof(f280,plain,(
% 2.26/0.67    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2))),
% 2.26/0.67    inference(resolution,[],[f275,f66])).
% 2.26/0.67  fof(f275,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2))) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f274,f62])).
% 2.26/0.67  fof(f274,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f273,f63])).
% 2.26/0.67  fof(f273,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f270,f64])).
% 2.26/0.67  fof(f270,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(resolution,[],[f141,f66])).
% 2.26/0.67  fof(f141,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f140,f62])).
% 2.26/0.67  fof(f140,plain,(
% 2.26/0.67    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f139,f63])).
% 2.26/0.67  fof(f139,plain,(
% 2.26/0.67    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f138,f64])).
% 2.26/0.67  fof(f138,plain,(
% 2.26/0.67    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f137,f67])).
% 2.26/0.67  fof(f137,plain,(
% 2.26/0.67    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f128,f68])).
% 2.26/0.67  fof(f128,plain,(
% 2.26/0.67    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK0,sK1,X1,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(resolution,[],[f69,f94])).
% 2.26/0.67  fof(f94,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f54])).
% 2.26/0.67  fof(f54,plain,(
% 2.26/0.67    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f53])).
% 2.26/0.67  fof(f53,plain,(
% 2.26/0.67    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f11])).
% 2.26/0.67  fof(f11,axiom,(
% 2.26/0.67    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.26/0.67  fof(f1203,plain,(
% 2.26/0.67    ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_16)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1202,f492])).
% 2.26/0.67  fof(f492,plain,(
% 2.26/0.67    v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_16),
% 2.26/0.67    inference(backward_demodulation,[],[f311,f490])).
% 2.26/0.67  fof(f311,plain,(
% 2.26/0.67    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_16),
% 2.26/0.67    inference(avatar_component_clause,[],[f310])).
% 2.26/0.67  fof(f1202,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | r2_hidden(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(resolution,[],[f749,f493])).
% 2.26/0.67  fof(f493,plain,(
% 2.26/0.67    m1_subset_1(k2_tmap_1(sK1,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.26/0.67    inference(backward_demodulation,[],[f296,f490])).
% 2.26/0.67  fof(f296,plain,(
% 2.26/0.67    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.26/0.67    inference(resolution,[],[f287,f66])).
% 2.26/0.67  fof(f287,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f286,f62])).
% 2.26/0.67  fof(f286,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f285,f63])).
% 2.26/0.67  fof(f285,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f282,f64])).
% 2.26/0.67  fof(f282,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.26/0.67    inference(resolution,[],[f146,f66])).
% 2.26/0.67  fof(f146,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~m1_pre_topc(sK1,X2) | ~m1_pre_topc(X3,X2) | m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f145,f62])).
% 2.26/0.67  fof(f145,plain,(
% 2.26/0.67    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f144,f63])).
% 2.26/0.67  fof(f144,plain,(
% 2.26/0.67    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f143,f64])).
% 2.26/0.67  fof(f143,plain,(
% 2.26/0.67    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f142,f67])).
% 2.26/0.67  fof(f142,plain,(
% 2.26/0.67    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f129,f68])).
% 2.26/0.67  fof(f129,plain,(
% 2.26/0.67    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK0,sK1,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.26/0.67    inference(resolution,[],[f69,f96])).
% 2.26/0.67  fof(f96,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f54])).
% 2.26/0.67  fof(f749,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f748,f62])).
% 2.26/0.67  fof(f748,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f747,f63])).
% 2.26/0.67  fof(f747,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f746,f64])).
% 2.26/0.67  fof(f746,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f745,f65])).
% 2.26/0.67  fof(f745,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f744,f108])).
% 2.26/0.67  fof(f744,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f743,f206])).
% 2.26/0.67  fof(f743,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_12),
% 2.26/0.67    inference(subsumption_resolution,[],[f735,f111])).
% 2.26/0.67  fof(f735,plain,(
% 2.26/0.67    ( ! [X2,X3] : (~v1_funct_1(k2_tmap_1(X2,sK0,X3,sK1)) | ~v1_funct_2(k2_tmap_1(X2,sK0,X3,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X2,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X2,sK0,X3,sK1) | r2_hidden(sK3(sK0,X2,sK1,X3,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK1,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_12),
% 2.26/0.67    inference(resolution,[],[f243,f80])).
% 2.26/0.67  fof(f80,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f60])).
% 2.26/0.67  fof(f1192,plain,(
% 2.26/0.67    ~spl4_16 | spl4_84),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f1191])).
% 2.26/0.67  fof(f1191,plain,(
% 2.26/0.67    $false | (~spl4_16 | spl4_84)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1129,f492])).
% 2.26/0.67  fof(f1129,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_84),
% 2.26/0.67    inference(avatar_component_clause,[],[f1127])).
% 2.26/0.67  fof(f1127,plain,(
% 2.26/0.67    spl4_84 <=> v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 2.26/0.67  fof(f1130,plain,(
% 2.26/0.67    spl4_81 | spl4_83 | ~spl4_84 | ~spl4_7 | ~spl4_12 | ~spl4_37),
% 2.26/0.67    inference(avatar_split_clause,[],[f1121,f531,f242,f205,f1127,f1123,f1064])).
% 2.26/0.67  fof(f1121,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | (~spl4_7 | ~spl4_12 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1120,f65])).
% 2.26/0.67  fof(f1120,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1119,f113])).
% 2.26/0.67  fof(f1119,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1118,f115])).
% 2.26/0.67  fof(f1118,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12 | ~spl4_37)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1117,f532])).
% 2.26/0.67  fof(f1117,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1116,f67])).
% 2.26/0.67  fof(f1116,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1115,f68])).
% 2.26/0.67  fof(f1115,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1114,f69])).
% 2.26/0.67  fof(f1114,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f1103,f494])).
% 2.26/0.67  fof(f1103,plain,(
% 2.26/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,sK2,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(sK1,sK0,sK2,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,sK2,sK1) | m1_subset_1(sK3(sK0,sK1,sK1,sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(resolution,[],[f493,f742])).
% 2.26/0.67  fof(f742,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f741,f62])).
% 2.26/0.67  fof(f741,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f740,f63])).
% 2.26/0.67  fof(f740,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f739,f64])).
% 2.26/0.67  fof(f739,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f738,f65])).
% 2.26/0.67  fof(f738,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f737,f108])).
% 2.26/0.67  fof(f737,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_7 | ~spl4_12)),
% 2.26/0.67    inference(subsumption_resolution,[],[f736,f206])).
% 2.26/0.67  fof(f736,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_12),
% 2.26/0.67    inference(subsumption_resolution,[],[f734,f111])).
% 2.26/0.67  fof(f734,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~v1_funct_1(k2_tmap_1(X0,sK0,X1,sK1)) | ~v1_funct_2(k2_tmap_1(X0,sK0,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tmap_1(X0,sK0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(X0,sK0,X1,sK1) | m1_subset_1(sK3(sK0,X0,sK1,X1,k4_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_12),
% 2.26/0.67    inference(resolution,[],[f243,f79])).
% 2.26/0.67  fof(f79,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f60])).
% 2.26/0.67  fof(f555,plain,(
% 2.26/0.67    spl4_37),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f554])).
% 2.26/0.67  fof(f554,plain,(
% 2.26/0.67    $false | spl4_37),
% 2.26/0.67    inference(subsumption_resolution,[],[f553,f115])).
% 2.26/0.67  fof(f553,plain,(
% 2.26/0.67    ~l1_pre_topc(sK1) | spl4_37),
% 2.26/0.67    inference(resolution,[],[f533,f73])).
% 2.26/0.67  fof(f533,plain,(
% 2.26/0.67    ~m1_pre_topc(sK1,sK1) | spl4_37),
% 2.26/0.67    inference(avatar_component_clause,[],[f531])).
% 2.26/0.67  fof(f552,plain,(
% 2.26/0.67    ~spl4_37 | spl4_39 | spl4_17),
% 2.26/0.67    inference(avatar_split_clause,[],[f547,f314,f549,f531])).
% 2.26/0.67  fof(f547,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f546,f62])).
% 2.26/0.67  fof(f546,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f545,f63])).
% 2.26/0.67  fof(f545,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f544,f64])).
% 2.26/0.67  fof(f544,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f543,f113])).
% 2.26/0.67  fof(f543,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f542,f115])).
% 2.26/0.67  fof(f542,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f541,f65])).
% 2.26/0.67  fof(f541,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f540,f67])).
% 2.26/0.67  fof(f540,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f539,f68])).
% 2.26/0.67  fof(f539,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f519,f69])).
% 2.26/0.67  fof(f519,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f518])).
% 2.26/0.67  fof(f518,plain,(
% 2.26/0.67    r2_hidden(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(resolution,[],[f491,f80])).
% 2.26/0.67  fof(f538,plain,(
% 2.26/0.67    ~spl4_37 | spl4_38 | spl4_17),
% 2.26/0.67    inference(avatar_split_clause,[],[f529,f314,f535,f531])).
% 2.26/0.67  fof(f529,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f528,f62])).
% 2.26/0.67  fof(f528,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f527,f63])).
% 2.26/0.67  fof(f527,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f526,f64])).
% 2.26/0.67  fof(f526,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f525,f113])).
% 2.26/0.67  fof(f525,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f524,f115])).
% 2.26/0.67  fof(f524,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f523,f65])).
% 2.26/0.67  fof(f523,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f522,f67])).
% 2.26/0.67  fof(f522,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f521,f68])).
% 2.26/0.67  fof(f521,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(subsumption_resolution,[],[f520,f69])).
% 2.26/0.67  fof(f520,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f517])).
% 2.26/0.67  fof(f517,plain,(
% 2.26/0.67    m1_subset_1(sK3(sK0,sK1,sK1,sK2,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_17),
% 2.26/0.67    inference(resolution,[],[f491,f79])).
% 2.26/0.67  fof(f384,plain,(
% 2.26/0.67    spl4_16),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f383])).
% 2.26/0.67  fof(f383,plain,(
% 2.26/0.67    $false | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f382,f62])).
% 2.26/0.67  fof(f382,plain,(
% 2.26/0.67    v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f381,f63])).
% 2.26/0.67  fof(f381,plain,(
% 2.26/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f380,f64])).
% 2.26/0.67  fof(f380,plain,(
% 2.26/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f379,f66])).
% 2.26/0.67  fof(f379,plain,(
% 2.26/0.67    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f378,f67])).
% 2.26/0.67  fof(f378,plain,(
% 2.26/0.67    ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f377,f68])).
% 2.26/0.67  fof(f377,plain,(
% 2.26/0.67    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(subsumption_resolution,[],[f376,f69])).
% 2.26/0.67  fof(f376,plain,(
% 2.26/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(duplicate_literal_removal,[],[f375])).
% 2.26/0.67  fof(f375,plain,(
% 2.26/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_16),
% 2.26/0.67    inference(resolution,[],[f312,f95])).
% 2.26/0.67  fof(f95,plain,(
% 2.26/0.67    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f54])).
% 2.26/0.67  fof(f312,plain,(
% 2.26/0.67    ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_16),
% 2.26/0.67    inference(avatar_component_clause,[],[f310])).
% 2.26/0.67  fof(f321,plain,(
% 2.26/0.67    ~spl4_16 | ~spl4_17 | spl4_18),
% 2.26/0.67    inference(avatar_split_clause,[],[f308,f318,f314,f310])).
% 2.26/0.67  fof(f308,plain,(
% 2.26/0.67    sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.26/0.67    inference(subsumption_resolution,[],[f298,f280])).
% 2.26/0.67  fof(f298,plain,(
% 2.26/0.67    sK2 = k3_tmap_1(sK0,sK0,sK1,sK1,sK2) | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,sK2),sK2) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,sK2))),
% 2.26/0.67    inference(resolution,[],[f296,f162])).
% 2.26/0.67  fof(f162,plain,(
% 2.26/0.67    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK2 = X7 | ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,sK2) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X7)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f161,f67])).
% 2.26/0.67  fof(f161,plain,(
% 2.26/0.67    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,sK2) | sK2 = X7 | ~v1_funct_1(sK2) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X7)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f132,f68])).
% 2.26/0.67  fof(f132,plain,(
% 2.26/0.67    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,sK2) | sK2 = X7 | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X7)) )),
% 2.26/0.67    inference(resolution,[],[f69,f92])).
% 2.26/0.67  fof(f92,plain,(
% 2.26/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f61])).
% 2.26/0.67  fof(f267,plain,(
% 2.26/0.67    spl4_7),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f266])).
% 2.26/0.67  fof(f266,plain,(
% 2.26/0.67    $false | spl4_7),
% 2.26/0.67    inference(subsumption_resolution,[],[f265,f62])).
% 2.26/0.67  fof(f265,plain,(
% 2.26/0.67    v2_struct_0(sK0) | spl4_7),
% 2.26/0.67    inference(subsumption_resolution,[],[f264,f63])).
% 2.26/0.67  fof(f264,plain,(
% 2.26/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_7),
% 2.26/0.67    inference(subsumption_resolution,[],[f263,f64])).
% 2.26/0.67  fof(f263,plain,(
% 2.26/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_7),
% 2.26/0.67    inference(subsumption_resolution,[],[f262,f66])).
% 2.26/0.67  fof(f262,plain,(
% 2.26/0.67    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_7),
% 2.26/0.67    inference(resolution,[],[f207,f88])).
% 2.26/0.67  fof(f88,plain,(
% 2.26/0.67    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f46])).
% 2.26/0.67  fof(f207,plain,(
% 2.26/0.67    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_7),
% 2.26/0.67    inference(avatar_component_clause,[],[f205])).
% 2.26/0.67  fof(f244,plain,(
% 2.26/0.67    ~spl4_7 | spl4_12),
% 2.26/0.67    inference(avatar_split_clause,[],[f240,f242,f205])).
% 2.26/0.67  fof(f240,plain,(
% 2.26/0.67    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = X7 | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X7)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f195,f108])).
% 2.26/0.67  fof(f195,plain,(
% 2.26/0.67    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X7,k4_tmap_1(sK0,sK1)) | k4_tmap_1(sK0,sK1) = X7 | ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X7)) )),
% 2.26/0.67    inference(resolution,[],[f111,f92])).
% 2.26/0.67  fof(f187,plain,(
% 2.26/0.67    ~spl4_3),
% 2.26/0.67    inference(avatar_contradiction_clause,[],[f186])).
% 2.26/0.67  fof(f186,plain,(
% 2.26/0.67    $false | ~spl4_3),
% 2.26/0.67    inference(subsumption_resolution,[],[f185,f65])).
% 2.26/0.67  fof(f185,plain,(
% 2.26/0.67    v2_struct_0(sK1) | ~spl4_3),
% 2.26/0.67    inference(subsumption_resolution,[],[f184,f116])).
% 2.26/0.67  fof(f116,plain,(
% 2.26/0.67    l1_struct_0(sK1)),
% 2.26/0.67    inference(resolution,[],[f115,f72])).
% 2.26/0.67  fof(f72,plain,(
% 2.26/0.67    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f23])).
% 2.26/0.67  fof(f23,plain,(
% 2.26/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.26/0.67    inference(ennf_transformation,[],[f6])).
% 2.26/0.67  fof(f6,axiom,(
% 2.26/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.26/0.67  fof(f184,plain,(
% 2.26/0.67    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl4_3),
% 2.26/0.67    inference(resolution,[],[f170,f76])).
% 2.26/0.67  fof(f76,plain,(
% 2.26/0.67    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f28])).
% 2.26/0.67  fof(f28,plain,(
% 2.26/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f27])).
% 2.26/0.67  fof(f27,plain,(
% 2.26/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f8])).
% 2.26/0.67  fof(f8,axiom,(
% 2.26/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.26/0.67  fof(f170,plain,(
% 2.26/0.67    v1_xboole_0(u1_struct_0(sK1)) | ~spl4_3),
% 2.26/0.67    inference(avatar_component_clause,[],[f168])).
% 2.26/0.67  fof(f168,plain,(
% 2.26/0.67    spl4_3 <=> v1_xboole_0(u1_struct_0(sK1))),
% 2.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.26/0.67  fof(f174,plain,(
% 2.26/0.67    spl4_3 | spl4_4),
% 2.26/0.67    inference(avatar_split_clause,[],[f166,f172,f168])).
% 2.26/0.67  fof(f166,plain,(
% 2.26/0.67    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8) | v1_xboole_0(u1_struct_0(sK1))) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f165,f67])).
% 2.26/0.67  fof(f165,plain,(
% 2.26/0.67    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(sK1))) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f134,f68])).
% 2.26/0.67  fof(f134,plain,(
% 2.26/0.67    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X8) = k1_funct_1(sK2,X8) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(sK1))) )),
% 2.26/0.67    inference(resolution,[],[f69,f91])).
% 2.26/0.68  % (16203)Refutation not found, incomplete strategy% (16203)------------------------------
% 2.26/0.68  % (16203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.68  fof(f91,plain,(
% 2.26/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f50])).
% 2.26/0.68  fof(f50,plain,(
% 2.26/0.68    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.26/0.68    inference(flattening,[],[f49])).
% 2.26/0.68  fof(f49,plain,(
% 2.26/0.68    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.26/0.68    inference(ennf_transformation,[],[f3])).
% 2.26/0.68  fof(f3,axiom,(
% 2.26/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 2.26/0.68  % SZS output end Proof for theBenchmark
% 2.26/0.68  % (16195)------------------------------
% 2.26/0.68  % (16195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.68  % (16195)Termination reason: Refutation
% 2.26/0.68  
% 2.26/0.68  % (16195)Memory used [KB]: 12153
% 2.26/0.68  % (16195)Time elapsed: 0.255 s
% 2.26/0.68  % (16195)------------------------------
% 2.26/0.68  % (16195)------------------------------
% 2.26/0.68  % (16191)Success in time 0.323 s
%------------------------------------------------------------------------------

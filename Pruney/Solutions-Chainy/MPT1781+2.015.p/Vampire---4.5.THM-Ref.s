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
% DateTime   : Thu Dec  3 13:19:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  212 (1885 expanded)
%              Number of leaves         :   28 ( 686 expanded)
%              Depth                    :   24
%              Number of atoms          : 1033 (18732 expanded)
%              Number of equality atoms :  143 (1958 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f746,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f315,f488,f501,f610,f650,f667,f674,f745])).

fof(f745,plain,
    ( ~ spl5_2
    | ~ spl5_20
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_20
    | spl5_31 ),
    inference(subsumption_resolution,[],[f743,f724])).

fof(f724,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f723,f500])).

fof(f500,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl5_20
  <=> r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f723,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f719,f127])).

fof(f127,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_2
  <=> u1_struct_0(sK1) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f719,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f707,f61])).

fof(f61,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f707,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f706,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f706,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f705,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f705,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f687,f57])).

fof(f57,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f687,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f684,f326])).

fof(f326,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_relat_1(sK2))
        | m1_subset_1(X2,u1_struct_0(X3))
        | ~ m1_pre_topc(sK1,X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f323,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f323,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_relat_1(sK2))
        | m1_subset_1(X2,u1_struct_0(X3))
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_2 ),
    inference(superposition,[],[f68,f127])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f684,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | ~ spl5_20 ),
    inference(resolution,[],[f500,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f743,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl5_2
    | ~ spl5_20
    | spl5_31 ),
    inference(superposition,[],[f673,f729])).

fof(f729,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f728,f53])).

fof(f728,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f727,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f727,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f726,f55])).

fof(f726,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f725,f57])).

fof(f725,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f720,f500])).

fof(f720,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f707,f325])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | k1_funct_1(k4_tmap_1(X1,sK1),X0) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f322,f56])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(k4_tmap_1(X1,sK1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_2 ),
    inference(superposition,[],[f67,f127])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f673,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl5_31
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f674,plain,
    ( spl5_19
    | ~ spl5_31
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f669,f125,f121,f671,f494])).

fof(f494,plain,
    ( spl5_19
  <=> r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f121,plain,
    ( spl5_1
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f669,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f668,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f99,f73])).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f99,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f668,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f513,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f513,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f389,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f389,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(k4_tmap_1(sK0,sK1),X1))
        | r1_tarski(k4_tmap_1(sK0,sK1),X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f388,f200])).

fof(f200,plain,(
    v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f180,f73])).

fof(f180,plain,
    ( v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(resolution,[],[f116,f65])).

fof(f116,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f54])).

fof(f114,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f55])).

fof(f113,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f77,f57])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f388,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(k4_tmap_1(sK0,sK1),X1))
        | r1_tarski(k4_tmap_1(sK0,sK1),X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f382,f105])).

fof(f105,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f104,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f54])).

fof(f103,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f102,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f75,f57])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k4_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f382,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(k4_tmap_1(sK0,sK1),X1))
        | r1_tarski(k4_tmap_1(sK0,sK1),X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f72,f371])).

fof(f371,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f362,f370])).

fof(f370,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f369,f122])).

fof(f122,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f369,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f361,f320])).

fof(f320,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f112,f127])).

fof(f112,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f111,f53])).

fof(f111,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f110,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f55])).

fof(f109,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f76,f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f361,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f321,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f321,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))
    | ~ spl5_2 ),
    inference(superposition,[],[f116,f127])).

fof(f362,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f321,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(f667,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19
    | spl5_30 ),
    inference(subsumption_resolution,[],[f665,f100])).

fof(f665,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19
    | spl5_30 ),
    inference(subsumption_resolution,[],[f664,f58])).

fof(f664,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19
    | spl5_30 ),
    inference(subsumption_resolution,[],[f662,f649])).

fof(f649,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl5_30
  <=> k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f662,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(resolution,[],[f651,f496])).

fof(f496,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f494])).

fof(f651,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
        | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK3(sK2,k4_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f487,f395])).

fof(f395,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
        | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X5) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f394,f200])).

fof(f394,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
        | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f385,f105])).

fof(f385,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
        | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f70,f371])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f487,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl5_18
  <=> r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f650,plain,
    ( spl5_17
    | ~ spl5_30
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f645,f125,f121,f647,f481])).

fof(f481,plain,
    ( spl5_17
  <=> r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f645,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f644,f100])).

fof(f644,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f510,f58])).

fof(f510,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f387,f91])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
        | k1_funct_1(X0,sK3(X0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X0,k4_tmap_1(sK0,sK1)))
        | r1_tarski(X0,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f386,f200])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
        | k1_funct_1(X0,sK3(X0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X0,k4_tmap_1(sK0,sK1)))
        | r1_tarski(X0,k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f381,f105])).

fof(f381,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
        | k1_funct_1(X0,sK3(X0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X0,k4_tmap_1(sK0,sK1)))
        | r1_tarski(X0,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f72,f371])).

fof(f610,plain,
    ( ~ spl5_2
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f583,f334])).

fof(f334,plain,
    ( r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2)
    | ~ spl5_2 ),
    inference(global_subsumption,[],[f232])).

fof(f232,plain,
    ( r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f231,f58])).

fof(f231,plain,
    ( r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f230,f158])).

fof(f158,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f59,f127])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f230,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK0))
    | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f221])).

fof(f221,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK0))
    | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2)
    | k1_funct_1(sK2,sK4(k1_relat_1(sK2),sK2,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),sK2,sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f157,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(sK0))
        | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),X0,sK2)
        | k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f153,f127])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))
        | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),X0,sK2)
        | k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f152,f127])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),X0,sK2)
        | k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f151,f127])).

fof(f151,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f150,f127])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2)
      | k1_funct_1(X0,sK4(u1_struct_0(sK1),X0,sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),X0,sK2))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f149,f58])).

fof(f149,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(u1_struct_0(sK1),X0,sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),X0,sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f148,f59])).

fof(f148,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(u1_struct_0(sK1),X0,sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),X0,sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f90,f60])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
        & m1_subset_1(sK4(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))
    | ~ spl5_2 ),
    inference(superposition,[],[f60,f127])).

fof(f583,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2)
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(superposition,[],[f318,f509])).

fof(f509,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f503,f496])).

fof(f503,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f483,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f483,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f481])).

fof(f318,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f62,f127])).

fof(f62,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f501,plain,
    ( spl5_19
    | spl5_20
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f492,f125,f121,f498,f494])).

fof(f492,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f491,f100])).

fof(f491,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f489,f58])).

fof(f489,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f393,f91])).

fof(f393,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
        | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X3),k1_relat_1(sK2))
        | r1_tarski(k4_tmap_1(sK0,sK1),X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f392,f200])).

fof(f392,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
        | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X3),k1_relat_1(sK2))
        | r1_tarski(k4_tmap_1(sK0,sK1),X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f384,f105])).

fof(f384,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
        | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X3),k1_relat_1(sK2))
        | r1_tarski(k4_tmap_1(sK0,sK1),X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f71,f371])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f488,plain,
    ( spl5_17
    | spl5_18
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f479,f125,f121,f485,f481])).

fof(f479,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f478,f100])).

fof(f478,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f476,f58])).

fof(f476,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f391,f91])).

fof(f391,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
        | r2_hidden(sK3(X2,k4_tmap_1(sK0,sK1)),k1_relat_1(X2))
        | r1_tarski(X2,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f390,f200])).

fof(f390,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
        | r2_hidden(sK3(X2,k4_tmap_1(sK0,sK1)),k1_relat_1(X2))
        | r1_tarski(X2,k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f383,f105])).

fof(f383,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
        | r2_hidden(sK3(X2,k4_tmap_1(sK0,sK1)),k1_relat_1(X2))
        | r1_tarski(X2,k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f71,f371])).

fof(f315,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f313,f53])).

fof(f313,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f312,f98])).

fof(f98,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f312,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f309,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f309,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(superposition,[],[f66,f123])).

fof(f123,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f128,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f118,f106])).

fof(f106,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f81,f60])).

fof(f118,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) ),
    inference(subsumption_resolution,[],[f117,f59])).

fof(f117,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) ),
    inference(resolution,[],[f82,f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:36:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (19960)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (19968)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  % (19957)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (19955)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (19963)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (19953)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (19966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (19956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (19962)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (19961)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (19952)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (19970)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (19971)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (19958)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (19952)Refutation not found, incomplete strategy% (19952)------------------------------
% 0.22/0.52  % (19952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19952)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19952)Memory used [KB]: 10618
% 0.22/0.52  % (19952)Time elapsed: 0.105 s
% 0.22/0.52  % (19952)------------------------------
% 0.22/0.52  % (19952)------------------------------
% 0.22/0.52  % (19976)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (19977)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (19965)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (19974)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (19973)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (19954)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (19972)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (19964)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (19975)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (19967)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (19969)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (19959)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (19959)Refutation not found, incomplete strategy% (19959)------------------------------
% 0.22/0.54  % (19959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19959)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (19959)Memory used [KB]: 1791
% 0.22/0.54  % (19959)Time elapsed: 0.139 s
% 0.22/0.54  % (19959)------------------------------
% 0.22/0.54  % (19959)------------------------------
% 0.22/0.55  % (19962)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f746,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f128,f315,f488,f501,f610,f650,f667,f674,f745])).
% 0.22/0.55  fof(f745,plain,(
% 0.22/0.55    ~spl5_2 | ~spl5_20 | spl5_31),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f744])).
% 0.22/0.55  fof(f744,plain,(
% 0.22/0.55    $false | (~spl5_2 | ~spl5_20 | spl5_31)),
% 0.22/0.55    inference(subsumption_resolution,[],[f743,f724])).
% 0.22/0.56  fof(f724,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | (~spl5_2 | ~spl5_20)),
% 0.22/0.56    inference(subsumption_resolution,[],[f723,f500])).
% 0.22/0.56  fof(f500,plain,(
% 0.22/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | ~spl5_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f498])).
% 0.22/0.56  fof(f498,plain,(
% 0.22/0.56    spl5_20 <=> r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.56  fof(f723,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | (~spl5_2 | ~spl5_20)),
% 0.22/0.56    inference(forward_demodulation,[],[f719,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    u1_struct_0(sK1) = k1_relat_1(sK2) | ~spl5_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f125])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    spl5_2 <=> u1_struct_0(sK1) = k1_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.56  fof(f719,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | (~spl5_2 | ~spl5_20)),
% 0.22/0.56    inference(resolution,[],[f707,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f39,f38,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) & ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f16])).
% 1.55/0.56  fof(f16,negated_conjecture,(
% 1.55/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.55/0.56    inference(negated_conjecture,[],[f15])).
% 1.55/0.56  fof(f15,conjecture,(
% 1.55/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 1.55/0.56  fof(f707,plain,(
% 1.55/0.56    m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f706,f53])).
% 1.55/0.56  fof(f53,plain,(
% 1.55/0.56    ~v2_struct_0(sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f706,plain,(
% 1.55/0.56    m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f705,f55])).
% 1.55/0.56  fof(f55,plain,(
% 1.55/0.56    l1_pre_topc(sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f705,plain,(
% 1.55/0.56    m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(resolution,[],[f687,f57])).
% 1.55/0.56  fof(f57,plain,(
% 1.55/0.56    m1_pre_topc(sK1,sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f687,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_pre_topc(sK1,X0) | m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(resolution,[],[f684,f326])).
% 1.55/0.56  fof(f326,plain,(
% 1.55/0.56    ( ! [X2,X3] : (~m1_subset_1(X2,k1_relat_1(sK2)) | m1_subset_1(X2,u1_struct_0(X3)) | ~m1_pre_topc(sK1,X3) | ~l1_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_2),
% 1.55/0.56    inference(subsumption_resolution,[],[f323,f56])).
% 1.55/0.56  fof(f56,plain,(
% 1.55/0.56    ~v2_struct_0(sK1)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f323,plain,(
% 1.55/0.56    ( ! [X2,X3] : (~m1_subset_1(X2,k1_relat_1(sK2)) | m1_subset_1(X2,u1_struct_0(X3)) | ~m1_pre_topc(sK1,X3) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f68,f127])).
% 1.55/0.56  fof(f68,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f26])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/0.56    inference(flattening,[],[f25])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f12])).
% 1.55/0.56  fof(f12,axiom,(
% 1.55/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.55/0.56  fof(f684,plain,(
% 1.55/0.56    m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | ~spl5_20),
% 1.55/0.56    inference(resolution,[],[f500,f74])).
% 1.55/0.56  fof(f74,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f29])).
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.55/0.56    inference(ennf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.55/0.56  fof(f743,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | (~spl5_2 | ~spl5_20 | spl5_31)),
% 1.55/0.56    inference(superposition,[],[f673,f729])).
% 1.55/0.56  fof(f729,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f728,f53])).
% 1.55/0.56  fof(f728,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f727,f54])).
% 1.55/0.56  fof(f54,plain,(
% 1.55/0.56    v2_pre_topc(sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f727,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f726,f55])).
% 1.55/0.56  fof(f726,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f725,f57])).
% 1.55/0.56  fof(f725,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(subsumption_resolution,[],[f720,f500])).
% 1.55/0.56  fof(f720,plain,(
% 1.55/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20)),
% 1.55/0.56    inference(resolution,[],[f707,f325])).
% 1.55/0.56  fof(f325,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X1,sK1),X0) = X0 | ~r2_hidden(X0,k1_relat_1(sK2)) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_2),
% 1.55/0.56    inference(subsumption_resolution,[],[f322,f56])).
% 1.55/0.56  fof(f322,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(k4_tmap_1(X1,sK1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f67,f127])).
% 1.55/0.56  fof(f67,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f24])).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/0.56    inference(flattening,[],[f23])).
% 1.55/0.56  fof(f23,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f14])).
% 1.55/0.56  fof(f14,axiom,(
% 1.55/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 1.55/0.56  fof(f673,plain,(
% 1.55/0.56    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | spl5_31),
% 1.55/0.56    inference(avatar_component_clause,[],[f671])).
% 1.55/0.56  fof(f671,plain,(
% 1.55/0.56    spl5_31 <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.55/0.56  fof(f674,plain,(
% 1.55/0.56    spl5_19 | ~spl5_31 | spl5_1 | ~spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f669,f125,f121,f671,f494])).
% 1.55/0.56  fof(f494,plain,(
% 1.55/0.56    spl5_19 <=> r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.55/0.56  fof(f121,plain,(
% 1.55/0.56    spl5_1 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.55/0.56  fof(f669,plain,(
% 1.55/0.56    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f668,f100])).
% 1.55/0.56  fof(f100,plain,(
% 1.55/0.56    v1_relat_1(sK2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f99,f73])).
% 1.55/0.56  fof(f73,plain,(
% 1.55/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.55/0.56  fof(f99,plain,(
% 1.55/0.56    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),
% 1.55/0.56    inference(resolution,[],[f65,f60])).
% 1.55/0.56  fof(f60,plain,(
% 1.55/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f65,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f20])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f4])).
% 1.55/0.56  fof(f4,axiom,(
% 1.55/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.55/0.56  fof(f668,plain,(
% 1.55/0.56    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f513,f58])).
% 1.55/0.56  fof(f58,plain,(
% 1.55/0.56    v1_funct_1(sK2)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f513,plain,(
% 1.55/0.56    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(resolution,[],[f389,f91])).
% 1.55/0.56  fof(f91,plain,(
% 1.55/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.55/0.56    inference(equality_resolution,[],[f79])).
% 1.55/0.56  fof(f79,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f47])).
% 1.55/0.56  fof(f47,plain,(
% 1.55/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.56    inference(flattening,[],[f46])).
% 1.55/0.56  fof(f46,plain,(
% 1.55/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.56    inference(nnf_transformation,[],[f2])).
% 1.55/0.56  fof(f2,axiom,(
% 1.55/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.56  fof(f389,plain,(
% 1.55/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(k4_tmap_1(sK0,sK1),X1)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f388,f200])).
% 1.55/0.56  fof(f200,plain,(
% 1.55/0.56    v1_relat_1(k4_tmap_1(sK0,sK1))),
% 1.55/0.56    inference(subsumption_resolution,[],[f180,f73])).
% 1.55/0.56  fof(f180,plain,(
% 1.55/0.56    v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),
% 1.55/0.56    inference(resolution,[],[f116,f65])).
% 1.55/0.56  fof(f116,plain,(
% 1.55/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.55/0.56    inference(subsumption_resolution,[],[f115,f53])).
% 1.55/0.56  fof(f115,plain,(
% 1.55/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f114,f54])).
% 1.55/0.56  fof(f114,plain,(
% 1.55/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f113,f55])).
% 1.55/0.56  fof(f113,plain,(
% 1.55/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f77,f57])).
% 1.55/0.56  fof(f77,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f31])).
% 1.55/0.56  fof(f31,plain,(
% 1.55/0.56    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/0.56    inference(flattening,[],[f30])).
% 1.55/0.56  fof(f30,plain,(
% 1.55/0.56    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f13])).
% 1.55/0.56  fof(f13,axiom,(
% 1.55/0.56    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 1.55/0.56  fof(f388,plain,(
% 1.55/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(k4_tmap_1(sK0,sK1),X1)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f382,f105])).
% 1.55/0.56  fof(f105,plain,(
% 1.55/0.56    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.55/0.56    inference(subsumption_resolution,[],[f104,f53])).
% 1.55/0.56  fof(f104,plain,(
% 1.55/0.56    v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f103,f54])).
% 1.55/0.56  fof(f103,plain,(
% 1.55/0.56    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f102,f55])).
% 1.55/0.56  fof(f102,plain,(
% 1.55/0.56    v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f75,f57])).
% 1.55/0.56  fof(f75,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k4_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f31])).
% 1.55/0.56  fof(f382,plain,(
% 1.55/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(k4_tmap_1(sK0,sK1),X1)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(superposition,[],[f72,f371])).
% 1.55/0.56  fof(f371,plain,(
% 1.55/0.56    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(forward_demodulation,[],[f362,f370])).
% 1.55/0.56  fof(f370,plain,(
% 1.55/0.56    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f369,f122])).
% 1.55/0.56  fof(f122,plain,(
% 1.55/0.56    k1_xboole_0 != u1_struct_0(sK0) | spl5_1),
% 1.55/0.56    inference(avatar_component_clause,[],[f121])).
% 1.55/0.56  fof(f369,plain,(
% 1.55/0.56    k1_xboole_0 = u1_struct_0(sK0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~spl5_2),
% 1.55/0.56    inference(subsumption_resolution,[],[f361,f320])).
% 1.55/0.56  fof(f320,plain,(
% 1.55/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f112,f127])).
% 1.55/0.56  fof(f112,plain,(
% 1.55/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.55/0.56    inference(subsumption_resolution,[],[f111,f53])).
% 1.55/0.56  fof(f111,plain,(
% 1.55/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f110,f54])).
% 1.55/0.56  fof(f110,plain,(
% 1.55/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f109,f55])).
% 1.55/0.56  fof(f109,plain,(
% 1.55/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f76,f57])).
% 1.55/0.56  fof(f76,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f31])).
% 1.55/0.56  fof(f361,plain,(
% 1.55/0.56    ~v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~spl5_2),
% 1.55/0.56    inference(resolution,[],[f321,f82])).
% 1.55/0.56  fof(f82,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.55/0.56    inference(cnf_transformation,[],[f48])).
% 1.55/0.56  fof(f48,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.56    inference(nnf_transformation,[],[f34])).
% 1.55/0.56  fof(f34,plain,(
% 1.55/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.56    inference(flattening,[],[f33])).
% 1.55/0.56  fof(f33,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.56    inference(ennf_transformation,[],[f7])).
% 1.55/0.56  fof(f7,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.55/0.56  fof(f321,plain,(
% 1.55/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f116,f127])).
% 1.55/0.56  fof(f362,plain,(
% 1.55/0.56    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~spl5_2),
% 1.55/0.56    inference(resolution,[],[f321,f81])).
% 1.55/0.56  fof(f81,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f32])).
% 1.55/0.56  fof(f32,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.56    inference(ennf_transformation,[],[f6])).
% 1.55/0.56  fof(f6,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.55/0.56  fof(f72,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f45])).
% 1.55/0.56  fof(f45,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 1.55/0.56  fof(f44,plain,(
% 1.55/0.56    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f43,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(rectify,[],[f42])).
% 1.55/0.56  fof(f42,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(flattening,[],[f41])).
% 1.55/0.56  fof(f41,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(nnf_transformation,[],[f28])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(flattening,[],[f27])).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f9])).
% 1.55/0.56  fof(f9,axiom,(
% 1.55/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).
% 1.55/0.56  fof(f667,plain,(
% 1.55/0.56    spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19 | spl5_30),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f666])).
% 1.55/0.56  fof(f666,plain,(
% 1.55/0.56    $false | (spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19 | spl5_30)),
% 1.55/0.56    inference(subsumption_resolution,[],[f665,f100])).
% 1.55/0.56  fof(f665,plain,(
% 1.55/0.56    ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19 | spl5_30)),
% 1.55/0.56    inference(subsumption_resolution,[],[f664,f58])).
% 1.55/0.56  fof(f664,plain,(
% 1.55/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19 | spl5_30)),
% 1.55/0.56    inference(subsumption_resolution,[],[f662,f649])).
% 1.55/0.56  fof(f649,plain,(
% 1.55/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | spl5_30),
% 1.55/0.56    inference(avatar_component_clause,[],[f647])).
% 1.55/0.56  fof(f647,plain,(
% 1.55/0.56    spl5_30 <=> k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.55/0.56  fof(f662,plain,(
% 1.55/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19)),
% 1.55/0.56    inference(resolution,[],[f651,f496])).
% 1.55/0.56  fof(f496,plain,(
% 1.55/0.56    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~spl5_19),
% 1.55/0.56    inference(avatar_component_clause,[],[f494])).
% 1.55/0.56  fof(f651,plain,(
% 1.55/0.56    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_18)),
% 1.55/0.56    inference(resolution,[],[f487,f395])).
% 1.55/0.56  fof(f395,plain,(
% 1.55/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f394,f200])).
% 1.55/0.56  fof(f394,plain,(
% 1.55/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f385,f105])).
% 1.55/0.56  fof(f385,plain,(
% 1.55/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(superposition,[],[f70,f371])).
% 1.55/0.56  fof(f70,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f45])).
% 1.55/0.56  fof(f487,plain,(
% 1.55/0.56    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | ~spl5_18),
% 1.55/0.56    inference(avatar_component_clause,[],[f485])).
% 1.55/0.56  fof(f485,plain,(
% 1.55/0.56    spl5_18 <=> r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.55/0.56  fof(f650,plain,(
% 1.55/0.56    spl5_17 | ~spl5_30 | spl5_1 | ~spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f645,f125,f121,f647,f481])).
% 1.55/0.56  fof(f481,plain,(
% 1.55/0.56    spl5_17 <=> r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.55/0.56  fof(f645,plain,(
% 1.55/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f644,f100])).
% 1.55/0.56  fof(f644,plain,(
% 1.55/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f510,f58])).
% 1.55/0.56  fof(f510,plain,(
% 1.55/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(resolution,[],[f387,f91])).
% 1.55/0.56  fof(f387,plain,(
% 1.55/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | k1_funct_1(X0,sK3(X0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X0,k4_tmap_1(sK0,sK1))) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f386,f200])).
% 1.55/0.56  fof(f386,plain,(
% 1.55/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | k1_funct_1(X0,sK3(X0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X0,k4_tmap_1(sK0,sK1))) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f381,f105])).
% 1.55/0.56  fof(f381,plain,(
% 1.55/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | k1_funct_1(X0,sK3(X0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X0,k4_tmap_1(sK0,sK1))) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(superposition,[],[f72,f371])).
% 1.55/0.56  fof(f610,plain,(
% 1.55/0.56    ~spl5_2 | ~spl5_17 | ~spl5_19),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f609])).
% 1.55/0.56  fof(f609,plain,(
% 1.55/0.56    $false | (~spl5_2 | ~spl5_17 | ~spl5_19)),
% 1.55/0.56    inference(subsumption_resolution,[],[f583,f334])).
% 1.55/0.56  fof(f334,plain,(
% 1.55/0.56    r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2) | ~spl5_2),
% 1.55/0.56    inference(global_subsumption,[],[f232])).
% 1.55/0.56  fof(f232,plain,(
% 1.55/0.56    r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2) | ~spl5_2),
% 1.55/0.56    inference(subsumption_resolution,[],[f231,f58])).
% 1.55/0.56  fof(f231,plain,(
% 1.55/0.56    r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2) | ~v1_funct_1(sK2) | ~spl5_2),
% 1.55/0.56    inference(subsumption_resolution,[],[f230,f158])).
% 1.55/0.56  fof(f158,plain,(
% 1.55/0.56    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK0)) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f59,f127])).
% 1.55/0.56  fof(f59,plain,(
% 1.55/0.56    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f230,plain,(
% 1.55/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK0)) | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2) | ~v1_funct_1(sK2) | ~spl5_2),
% 1.55/0.56    inference(trivial_inequality_removal,[],[f221])).
% 1.55/0.56  fof(f221,plain,(
% 1.55/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK0)) | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2) | k1_funct_1(sK2,sK4(k1_relat_1(sK2),sK2,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),sK2,sK2)) | ~v1_funct_1(sK2) | ~spl5_2),
% 1.55/0.56    inference(resolution,[],[f157,f154])).
% 1.55/0.56  fof(f154,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(sK0)) | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),X0,sK2) | k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2)) | ~v1_funct_1(X0)) ) | ~spl5_2),
% 1.55/0.56    inference(forward_demodulation,[],[f153,f127])).
% 1.55/0.56  fof(f153,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) | r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),X0,sK2) | k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) ) | ~spl5_2),
% 1.55/0.56    inference(forward_demodulation,[],[f152,f127])).
% 1.55/0.56  fof(f152,plain,(
% 1.55/0.56    ( ! [X0] : (r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),X0,sK2) | k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) ) | ~spl5_2),
% 1.55/0.56    inference(forward_demodulation,[],[f151,f127])).
% 1.55/0.56  fof(f151,plain,(
% 1.55/0.56    ( ! [X0] : (k1_funct_1(X0,sK4(k1_relat_1(sK2),X0,sK2)) != k1_funct_1(sK2,sK4(k1_relat_1(sK2),X0,sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) ) | ~spl5_2),
% 1.55/0.56    inference(forward_demodulation,[],[f150,f127])).
% 1.55/0.56  fof(f150,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2) | k1_funct_1(X0,sK4(u1_struct_0(sK1),X0,sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),X0,sK2)) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f149,f58])).
% 1.55/0.56  fof(f149,plain,(
% 1.55/0.56    ( ! [X0] : (k1_funct_1(X0,sK4(u1_struct_0(sK1),X0,sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),X0,sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f148,f59])).
% 1.55/0.56  fof(f148,plain,(
% 1.55/0.56    ( ! [X0] : (k1_funct_1(X0,sK4(u1_struct_0(sK1),X0,sK2)) != k1_funct_1(sK2,sK4(u1_struct_0(sK1),X0,sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0)) )),
% 1.55/0.56    inference(resolution,[],[f90,f60])).
% 1.55/0.56  fof(f90,plain,(
% 1.55/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) | r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f52])).
% 1.55/0.56  fof(f52,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 1.55/0.56  fof(f51,plain,(
% 1.55/0.56    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) & m1_subset_1(sK4(X0,X2,X3),X0)))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f50,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.55/0.56    inference(rectify,[],[f49])).
% 1.55/0.56  fof(f49,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.55/0.56    inference(nnf_transformation,[],[f36])).
% 1.55/0.56  fof(f36,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.55/0.56    inference(flattening,[],[f35])).
% 1.55/0.56  fof(f35,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.55/0.56    inference(ennf_transformation,[],[f8])).
% 1.55/0.56  fof(f8,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).
% 1.55/0.56  fof(f157,plain,(
% 1.55/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f60,f127])).
% 1.55/0.56  fof(f583,plain,(
% 1.55/0.56    ~r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),sK2,sK2) | (~spl5_2 | ~spl5_17 | ~spl5_19)),
% 1.55/0.56    inference(superposition,[],[f318,f509])).
% 1.55/0.56  fof(f509,plain,(
% 1.55/0.56    k4_tmap_1(sK0,sK1) = sK2 | (~spl5_17 | ~spl5_19)),
% 1.55/0.56    inference(subsumption_resolution,[],[f503,f496])).
% 1.55/0.56  fof(f503,plain,(
% 1.55/0.56    k4_tmap_1(sK0,sK1) = sK2 | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~spl5_17),
% 1.55/0.56    inference(resolution,[],[f483,f80])).
% 1.55/0.56  fof(f80,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f47])).
% 1.55/0.56  fof(f483,plain,(
% 1.55/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~spl5_17),
% 1.55/0.56    inference(avatar_component_clause,[],[f481])).
% 1.55/0.56  fof(f318,plain,(
% 1.55/0.56    ~r2_funct_2(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f62,f127])).
% 1.55/0.56  fof(f62,plain,(
% 1.55/0.56    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 1.55/0.56    inference(cnf_transformation,[],[f40])).
% 1.55/0.56  fof(f501,plain,(
% 1.55/0.56    spl5_19 | spl5_20 | spl5_1 | ~spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f492,f125,f121,f498,f494])).
% 1.55/0.56  fof(f492,plain,(
% 1.55/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f491,f100])).
% 1.55/0.56  fof(f491,plain,(
% 1.55/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f489,f58])).
% 1.55/0.56  fof(f489,plain,(
% 1.55/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(resolution,[],[f393,f91])).
% 1.55/0.56  fof(f393,plain,(
% 1.55/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X3),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f392,f200])).
% 1.55/0.56  fof(f392,plain,(
% 1.55/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X3),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f384,f105])).
% 1.55/0.56  fof(f384,plain,(
% 1.55/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X3),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(superposition,[],[f71,f371])).
% 1.55/0.56  fof(f71,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f45])).
% 1.55/0.56  fof(f488,plain,(
% 1.55/0.56    spl5_17 | spl5_18 | spl5_1 | ~spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f479,f125,f121,f485,f481])).
% 1.55/0.56  fof(f479,plain,(
% 1.55/0.56    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f478,f100])).
% 1.55/0.56  fof(f478,plain,(
% 1.55/0.56    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f476,f58])).
% 1.55/0.56  fof(f476,plain,(
% 1.55/0.56    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(resolution,[],[f391,f91])).
% 1.55/0.56  fof(f391,plain,(
% 1.55/0.56    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | r2_hidden(sK3(X2,k4_tmap_1(sK0,sK1)),k1_relat_1(X2)) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f390,f200])).
% 1.55/0.56  fof(f390,plain,(
% 1.55/0.56    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | r2_hidden(sK3(X2,k4_tmap_1(sK0,sK1)),k1_relat_1(X2)) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f383,f105])).
% 1.55/0.56  fof(f383,plain,(
% 1.55/0.56    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | r2_hidden(sK3(X2,k4_tmap_1(sK0,sK1)),k1_relat_1(X2)) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (spl5_1 | ~spl5_2)),
% 1.55/0.56    inference(superposition,[],[f71,f371])).
% 1.55/0.56  fof(f315,plain,(
% 1.55/0.56    ~spl5_1),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f314])).
% 1.55/0.56  fof(f314,plain,(
% 1.55/0.56    $false | ~spl5_1),
% 1.55/0.56    inference(subsumption_resolution,[],[f313,f53])).
% 1.55/0.56  fof(f313,plain,(
% 1.55/0.56    v2_struct_0(sK0) | ~spl5_1),
% 1.55/0.56    inference(subsumption_resolution,[],[f312,f98])).
% 1.55/0.56  fof(f98,plain,(
% 1.55/0.56    l1_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f64,f55])).
% 1.55/0.56  fof(f64,plain,(
% 1.55/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f19])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f10])).
% 1.55/0.56  fof(f10,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.55/0.56  fof(f312,plain,(
% 1.55/0.56    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 1.55/0.56    inference(subsumption_resolution,[],[f309,f63])).
% 1.55/0.56  fof(f63,plain,(
% 1.55/0.56    v1_xboole_0(k1_xboole_0)),
% 1.55/0.56    inference(cnf_transformation,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    v1_xboole_0(k1_xboole_0)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.55/0.56  fof(f309,plain,(
% 1.55/0.56    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 1.55/0.56    inference(superposition,[],[f66,f123])).
% 1.55/0.56  fof(f123,plain,(
% 1.55/0.56    k1_xboole_0 = u1_struct_0(sK0) | ~spl5_1),
% 1.55/0.56    inference(avatar_component_clause,[],[f121])).
% 1.55/0.56  fof(f66,plain,(
% 1.55/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f22])).
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.55/0.56    inference(flattening,[],[f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f11])).
% 1.55/0.56  fof(f11,axiom,(
% 1.55/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.55/0.56  fof(f128,plain,(
% 1.55/0.56    spl5_1 | spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f119,f125,f121])).
% 1.55/0.56  fof(f119,plain,(
% 1.55/0.56    u1_struct_0(sK1) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.55/0.56    inference(forward_demodulation,[],[f118,f106])).
% 1.55/0.56  fof(f106,plain,(
% 1.55/0.56    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2)),
% 1.55/0.56    inference(resolution,[],[f81,f60])).
% 1.55/0.56  fof(f118,plain,(
% 1.55/0.56    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f117,f59])).
% 1.55/0.56  fof(f117,plain,(
% 1.55/0.56    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)),
% 1.55/0.56    inference(resolution,[],[f82,f60])).
% 1.55/0.56  % SZS output end Proof for theBenchmark
% 1.55/0.56  % (19962)------------------------------
% 1.55/0.56  % (19962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (19962)Termination reason: Refutation
% 1.55/0.56  
% 1.55/0.56  % (19962)Memory used [KB]: 11001
% 1.55/0.56  % (19962)Time elapsed: 0.130 s
% 1.55/0.56  % (19962)------------------------------
% 1.55/0.56  % (19962)------------------------------
% 1.55/0.57  % (19951)Success in time 0.204 s
%------------------------------------------------------------------------------

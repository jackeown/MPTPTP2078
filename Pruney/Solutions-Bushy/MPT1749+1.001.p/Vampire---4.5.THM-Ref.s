%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1749+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:28 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 938 expanded)
%              Number of leaves         :   22 ( 444 expanded)
%              Depth                    :   22
%              Number of atoms          :  886 (15300 expanded)
%              Number of equality atoms :  102 (1134 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f390,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f148,f170,f174,f181,f188,f312,f376,f389])).

fof(f389,plain,(
    ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f387,f96])).

fof(f96,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f39,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(X2))
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(sK2))
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                | ~ r2_hidden(X5,u1_struct_0(sK2))
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
              | ~ r2_hidden(X5,u1_struct_0(sK2))
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
        & ! [X5] :
            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
            | ~ r2_hidden(X5,u1_struct_0(sK2))
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
      & ! [X5] :
          ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,u1_struct_0(sK2))
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f95,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f92,f56])).

fof(f56,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f387,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ spl6_19 ),
    inference(superposition,[],[f59,f311])).

fof(f311,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_19
  <=> k2_tmap_1(sK1,sK0,sK3,sK2) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f59,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f376,plain,
    ( spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | spl6_19 ),
    inference(subsumption_resolution,[],[f374,f307])).

fof(f307,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl6_18
  <=> m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f374,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | spl6_19 ),
    inference(subsumption_resolution,[],[f373,f368])).

fof(f368,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | spl6_2
    | ~ spl6_8
    | spl6_19 ),
    inference(subsumption_resolution,[],[f367,f310])).

fof(f310,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK4
    | spl6_19 ),
    inference(avatar_component_clause,[],[f309])).

fof(f367,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | spl6_2
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f366,f242])).

fof(f242,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f241,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f241,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f240,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f240,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f239,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f239,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f238,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f238,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f53])).

fof(f53,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f236,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f110,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f109,f48])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK1,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f366,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f365,f86])).

fof(f86,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f85,f49])).

fof(f85,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f65,f51])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f365,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f364,f53])).

fof(f364,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f363,f52])).

fof(f363,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f359,f122])).

fof(f122,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_2
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f359,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl6_8 ),
    inference(resolution,[],[f180,f54])).

fof(f180,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | k3_funct_2(X2,u1_struct_0(sK0),X3,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2)) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_8
  <=> ! [X3,X2] :
        ( k3_funct_2(X2,u1_struct_0(sK0),X3,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f373,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_9
    | spl6_19 ),
    inference(resolution,[],[f351,f58])).

fof(f58,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f351,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_9
    | spl6_19 ),
    inference(subsumption_resolution,[],[f350,f310])).

fof(f350,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f349,f242])).

fof(f349,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f348,f86])).

fof(f348,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f347,f53])).

fof(f347,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f346,f52])).

fof(f346,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f342,f122])).

fof(f342,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl6_9 ),
    inference(resolution,[],[f187,f54])).

fof(f187,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | r2_hidden(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2)) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_9
  <=> ! [X3,X2] :
        ( r2_hidden(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f312,plain,
    ( spl6_18
    | spl6_19
    | spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f303,f135,f121,f309,f305])).

fof(f135,plain,
    ( spl6_5
  <=> ! [X3,X2] :
        ( m1_subset_1(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),X2)
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f303,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK4
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f302,f242])).

fof(f302,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f301,f86])).

fof(f301,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f300,f53])).

fof(f300,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f299,f52])).

fof(f299,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f295,f122])).

fof(f295,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f136,f54])).

fof(f136,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | m1_subset_1(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),X2)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2)) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f188,plain,
    ( spl6_4
    | spl6_9
    | spl6_1 ),
    inference(avatar_split_clause,[],[f184,f117,f186,f131])).

fof(f131,plain,
    ( spl6_4
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f117,plain,
    ( spl6_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f184,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | v1_xboole_0(X2) )
    | spl6_1 ),
    inference(subsumption_resolution,[],[f183,f118])).

fof(f118,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f183,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f182,f55])).

fof(f182,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f139,f56])).

fof(f139,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

% (21023)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
                        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f41])).

fof(f41,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f181,plain,
    ( spl6_4
    | spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f177,f117,f179,f131])).

fof(f177,plain,
    ( ! [X2,X3] :
        ( k3_funct_2(X2,u1_struct_0(sK0),X3,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4))
        | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | v1_xboole_0(X2) )
    | spl6_1 ),
    inference(subsumption_resolution,[],[f176,f118])).

fof(f176,plain,(
    ! [X2,X3] :
      ( k3_funct_2(X2,u1_struct_0(sK0),X3,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4))
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f175,f55])).

fof(f175,plain,(
    ! [X2,X3] :
      ( k3_funct_2(X2,u1_struct_0(sK0),X3,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4))
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f141,f56])).

fof(f141,plain,(
    ! [X2,X3] :
      ( k3_funct_2(X2,u1_struct_0(sK0),X3,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4))
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f62,f57])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f174,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f172,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f172,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f171,f107])).

fof(f107,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f82,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f81,f49])).

fof(f81,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f171,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f133,f66])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f133,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f170,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f168,f44])).

fof(f168,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f167,f79])).

fof(f79,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f63,f46])).

fof(f167,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f119,f66])).

fof(f119,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f148,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f146,f47])).

fof(f146,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f145,f80])).

fof(f80,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f63,f49])).

fof(f145,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f123,f66])).

fof(f123,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f137,plain,
    ( spl6_1
    | spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f129,f135,f131,f117])).

fof(f129,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),X2)
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f128,f55])).

fof(f128,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),X2)
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f113,f56])).

fof(f113,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK5(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2),sK4),X2)
      | sK4 = k2_partfun1(X2,u1_struct_0(sK0),X3,u1_struct_0(sK2))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK0))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f60,f57])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:13:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 547 expanded)
%              Number of leaves         :   17 ( 204 expanded)
%              Depth                    :   27
%              Number of atoms          :  621 (5212 expanded)
%              Number of equality atoms :   61 ( 892 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f62,f66,f115,f131,f133,f172])).

fof(f172,plain,
    ( ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f170,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v3_pre_topc(sK2,sK1) )
    & ( ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v3_pre_topc(X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ v3_pre_topc(X2,X1) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | v3_pre_topc(X2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != X2
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v3_pre_topc(X2,sK1) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = X2
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v3_pre_topc(X2,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != X2
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v3_pre_topc(X2,sK1) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = X2
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v3_pre_topc(X2,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ! [X3] :
            ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v3_pre_topc(sK2,sK1) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = sK2
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v3_pre_topc(sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X4] :
        ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = sK2
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,X1)
              <~> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X2,X1)
                <=> ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

fof(f170,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f169,f125])).

fof(f125,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_6
  <=> r2_hidden(sK2,u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f169,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f168,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f168,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f167,f27])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f167,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f160,f157])).

fof(f157,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f156,f68])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f67,f26])).

fof(f67,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f156,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f155,f28])).

fof(f155,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f154,f125])).

fof(f154,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f153,f26])).

fof(f153,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f152,f27])).

fof(f152,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f148,f34])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK6(X0,sK1,sK2),sK0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f147,f28])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK6(X0,sK1,sK2),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f146,f125])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK6(X0,sK1,sK2),sK0)
        | ~ r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2 ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( sK2 != X1
        | ~ m1_subset_1(sK6(X0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK6(X0,sK1,X1),sK0)
        | ~ r2_hidden(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f135,f68])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( sK2 != X1
        | ~ m1_subset_1(sK6(X0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK6(X0,sK1,X1),sK0)
        | ~ r2_hidden(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f52,f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_2
  <=> ! [X3] :
        ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X2,X1,X0),X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f159,f43])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | v3_pre_topc(sK6(X2,X1,X0),X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | v3_pre_topc(sK6(X2,X1,X0),X2)
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f85,f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X2,X1,X0),u1_pre_topc(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | v3_pre_topc(sK6(X2,X1,X0),X2) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_pre_topc(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(sK6(X2,X1,X0),u1_pre_topc(X2))
      | v3_pre_topc(sK6(X2,X1,X0),X2) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_pre_topc(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(sK6(X2,X1,X0),u1_pre_topc(X2))
      | v3_pre_topc(sK6(X2,X1,X0),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f133,plain,
    ( spl7_6
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f132,f48,f118])).

fof(f48,plain,
    ( spl7_1
  <=> v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f132,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | r2_hidden(sK2,u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f69,f68])).

fof(f69,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f44,f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f131,plain,
    ( spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f130,f118,f48])).

fof(f130,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | v3_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f73,f68])).

fof(f73,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | v3_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f45,f28])).

fof(f115,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f112,f27])).

fof(f112,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f111,f72])).

fof(f72,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f71,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f70,f61])).

fof(f61,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_4
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f70,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f44,f65])).

fof(f65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f111,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f100,f65])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f99,f68])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f98,f76])).

fof(f76,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f75,f68])).

fof(f75,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f73,f49])).

fof(f49,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f93,f28])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f46,f57])).

fof(f57,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_3
  <=> sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f46,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,
    ( spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f29,f64,f48])).

fof(f29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f30,f60,f48])).

fof(f30,plain,
    ( v3_pre_topc(sK3,sK0)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f31,f56,f48])).

fof(f31,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f32,f51,f48])).

fof(f32,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10576)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (10576)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (10584)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f53,f58,f62,f66,f115,f131,f133,f172])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ~spl7_2 | ~spl7_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    $false | (~spl7_2 | ~spl7_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f170,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    (((! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(sK2,sK1)) & ((sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16,f15,f14,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1)) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(X2,X1)) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(X2,X1)) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK0)) => (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != X2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(X2,sK1)) & (? [X4] : (k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = X2 & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != X2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(X2,sK1)) & (? [X4] : (k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = X2 & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(sK2,sK1)) & (? [X4] : (k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = sK2 & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X4] : (k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = sK2 & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1)) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(rectify,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1)) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1)) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((v3_pre_topc(X2,X1) <~> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_2 | ~spl7_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f169,f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    r2_hidden(sK2,u1_pre_topc(sK1)) | ~spl7_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl7_6 <=> r2_hidden(sK2,u1_pre_topc(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_2 | ~spl7_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f168,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_2 | ~spl7_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f167,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_2 | ~spl7_6)),
% 0.21/0.47    inference(resolution,[],[f160,f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f26])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f27])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK1) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f155,f28])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f154,f125])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f26])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f27])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(resolution,[],[f148,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X5,u1_pre_topc(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & ((sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(X0,sK1,sK2),sK0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f28])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(X0,sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f125])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(X0,sK1,sK2),sK0) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_2),
% 0.21/0.48    inference(equality_resolution,[],[f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK2 != X1 | ~m1_subset_1(sK6(X0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(X0,sK1,X1),sK0) | ~r2_hidden(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f68])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK2 != X1 | ~m1_subset_1(sK6(X0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(X0,sK1,X1),sK0) | ~r2_hidden(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl7_2),
% 0.21/0.48    inference(superposition,[],[f52,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 | ~r2_hidden(X5,u1_pre_topc(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0)) ) | ~spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl7_2 <=> ! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X2,X1,X0),X2) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f43])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2) | ~r2_hidden(X0,u1_pre_topc(X1)) | v3_pre_topc(sK6(X2,X1,X0),X2) | ~l1_pre_topc(X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2) | ~r2_hidden(X0,u1_pre_topc(X1)) | v3_pre_topc(sK6(X2,X1,X0),X2) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) )),
% 0.21/0.48    inference(resolution,[],[f85,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X2,X1,X0),u1_pre_topc(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2) | ~r2_hidden(X0,u1_pre_topc(X1)) | v3_pre_topc(sK6(X2,X1,X0),X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f43])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~r2_hidden(sK6(X2,X1,X0),u1_pre_topc(X2)) | v3_pre_topc(sK6(X2,X1,X0),X2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~r2_hidden(sK6(X2,X1,X0),u1_pre_topc(X2)) | v3_pre_topc(sK6(X2,X1,X0),X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.48    inference(resolution,[],[f34,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl7_6 | ~spl7_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f132,f48,f118])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl7_1 <=> v3_pre_topc(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2,sK1) | r2_hidden(sK2,u1_pre_topc(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f68])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2,sK1) | r2_hidden(sK2,u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.21/0.48    inference(resolution,[],[f44,f28])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl7_1 | ~spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f118,f48])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~r2_hidden(sK2,u1_pre_topc(sK1)) | v3_pre_topc(sK2,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f68])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~r2_hidden(sK2,u1_pre_topc(sK1)) | v3_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.48    inference(resolution,[],[f45,f28])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f26])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f27])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    r2_hidden(sK3,u1_pre_topc(sK0)) | (~spl7_4 | ~spl7_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f26])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    r2_hidden(sK3,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | (~spl7_4 | ~spl7_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK0) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl7_4 <=> v3_pre_topc(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~v3_pre_topc(sK3,sK0) | r2_hidden(sK3,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~spl7_5),
% 0.21/0.48    inference(resolution,[],[f44,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~r2_hidden(sK3,u1_pre_topc(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_3 | ~spl7_5)),
% 0.21/0.48    inference(resolution,[],[f100,f65])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK3,u1_pre_topc(X0)) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (spl7_1 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f68])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK3,u1_pre_topc(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | (spl7_1 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~r2_hidden(sK2,u1_pre_topc(sK1)) | spl7_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f75,f68])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~r2_hidden(sK2,u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | spl7_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2,sK1) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK3,u1_pre_topc(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f28])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK3,u1_pre_topc(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK2,u1_pre_topc(sK1)) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl7_3),
% 0.21/0.48    inference(superposition,[],[f46,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl7_3 <=> sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X6,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,u1_pre_topc(X1)) | k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl7_1 | spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f64,f48])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl7_1 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f60,f48])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK0) | v3_pre_topc(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl7_1 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f56,f48])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) | v3_pre_topc(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~spl7_1 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f51,f48])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X3] : (k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2 | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10576)------------------------------
% 0.21/0.48  % (10576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10576)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10576)Memory used [KB]: 10746
% 0.21/0.48  % (10576)Time elapsed: 0.059 s
% 0.21/0.48  % (10576)------------------------------
% 0.21/0.48  % (10576)------------------------------
% 0.21/0.48  % (10570)Success in time 0.115 s
%------------------------------------------------------------------------------

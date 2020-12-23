%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1109+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  179 (4039 expanded)
%              Number of leaves         :   17 (1564 expanded)
%              Depth                    :   40
%              Number of atoms          :  759 (27931 expanded)
%              Number of equality atoms :  141 (7735 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1085,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1000,f1047,f1058,f1062,f1084])).

fof(f1084,plain,
    ( spl7_30
    | ~ spl7_31
    | ~ spl7_41
    | ~ spl7_42 ),
    inference(avatar_contradiction_clause,[],[f1083])).

fof(f1083,plain,
    ( $false
    | spl7_30
    | ~ spl7_31
    | ~ spl7_41
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f1082,f1051])).

fof(f1051,plain,
    ( m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1049,plain,
    ( spl7_42
  <=> m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f1082,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl7_30
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1081,f803])).

fof(f803,plain,
    ( ~ r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f802])).

fof(f802,plain,
    ( spl7_30
  <=> r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1081,plain,
    ( r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1080,f808])).

fof(f808,plain,
    ( r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl7_31
  <=> r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f1080,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1079,f741])).

fof(f741,plain,(
    m1_subset_1(sK4(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f740,f30])).

fof(f30,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    & m1_pre_topc(sK2,sK0)
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(X3,X1)
                    & m1_pre_topc(X2,X0)
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & l1_pre_topc(X3) )
                & l1_pre_topc(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,sK0)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(X3,X1)
                & m1_pre_topc(X2,sK0)
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & l1_pre_topc(X3) )
            & l1_pre_topc(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(X3,sK1)
              & m1_pre_topc(X2,sK0)
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & l1_pre_topc(X3) )
          & l1_pre_topc(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(X3,sK1)
            & m1_pre_topc(X2,sK0)
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & l1_pre_topc(X3) )
        & l1_pre_topc(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(X3,sK1)
          & m1_pre_topc(sK2,sK0)
          & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & l1_pre_topc(X3) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(X3,sK1)
        & m1_pre_topc(sK2,sK0)
        & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & l1_pre_topc(X3) )
   => ( ~ m1_pre_topc(sK3,sK1)
      & m1_pre_topc(sK2,sK0)
      & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,X0)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,X0)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( l1_pre_topc(X2)
               => ! [X3] :
                    ( l1_pre_topc(X3)
                   => ( ( m1_pre_topc(X2,X0)
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f740,plain,
    ( m1_subset_1(sK4(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f739,f36])).

fof(f36,plain,(
    ~ m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f739,plain,
    ( m1_subset_1(sK4(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f736,f68])).

fof(f68,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f736,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | m1_subset_1(sK4(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f313,f235])).

fof(f235,plain,(
    k2_struct_0(sK0) = k2_struct_0(sK1) ),
    inference(superposition,[],[f193,f65])).

fof(f65,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f55,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f193,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK1) = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f189,f58])).

fof(f58,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f29])).

fof(f189,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK1) = k2_struct_0(sK0) ),
    inference(superposition,[],[f101,f33])).

fof(f33,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
      | k2_struct_0(sK0) = X2 ) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f64,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f60,f58])).

fof(f60,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f313,plain,(
    ! [X7] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X7))
      | m1_subset_1(sK4(X7,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_pre_topc(sK3,X7)
      | ~ l1_pre_topc(X7) ) ),
    inference(forward_demodulation,[],[f312,f204])).

fof(f204,plain,(
    k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(superposition,[],[f171,f70])).

fof(f70,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f57,f37])).

fof(f57,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f171,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(trivial_inequality_removal,[],[f170])).

fof(f170,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f167,f69])).

fof(f69,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f38,f31])).

fof(f167,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(superposition,[],[f84,f34])).

fof(f34,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
      | k2_struct_0(sK2) = X2 ) ),
    inference(forward_demodulation,[],[f83,f69])).

fof(f83,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
      | u1_struct_0(sK2) = X2 ) ),
    inference(forward_demodulation,[],[f81,f69])).

fof(f81,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_struct_0(sK2) = X2 ) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f39,f31])).

fof(f312,plain,(
    ! [X7] :
      ( m1_subset_1(sK4(X7,sK3),k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X7))
      | m1_pre_topc(sK3,X7)
      | ~ l1_pre_topc(X7) ) ),
    inference(forward_demodulation,[],[f311,f70])).

fof(f311,plain,(
    ! [X7] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X7))
      | m1_subset_1(sK4(X7,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_pre_topc(sK3,X7)
      | ~ l1_pre_topc(X7) ) ),
    inference(subsumption_resolution,[],[f298,f32])).

fof(f298,plain,(
    ! [X7] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X7))
      | m1_subset_1(sK4(X7,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_pre_topc(sK3,X7)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f45,f204])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1079,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_41 ),
    inference(superposition,[],[f425,f1042])).

fof(f1042,plain,
    ( sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(sK1,sK3),k2_struct_0(sK2))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1040,plain,
    ( spl7_41
  <=> sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(sK1,sK3),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f425,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(k2_struct_0(sK2),X3,k2_struct_0(sK2)),u1_pre_topc(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f424,f31])).

fof(f424,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(k2_struct_0(sK2),X3,k2_struct_0(sK2)),u1_pre_topc(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f377,f35])).

fof(f377,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(k2_struct_0(sK2),X3,k2_struct_0(sK2)),u1_pre_topc(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_pre_topc(sK2,sK0)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f91,f69])).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X3),X2,k2_struct_0(X3)),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(X3),X2,k2_struct_0(X3)),u1_pre_topc(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_pre_topc(X3,sK0)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(X3),X2,k2_struct_0(X3)),u1_pre_topc(X3))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X3),X2,k2_struct_0(X3)),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X3,sK0)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f53,f58])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1062,plain,
    ( spl7_31
    | spl7_30 ),
    inference(avatar_split_clause,[],[f1061,f802,f806])).

fof(f1061,plain,
    ( r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f1060,f165])).

fof(f165,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(sK3) ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
    | u1_pre_topc(sK2) = u1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f161,f69])).

fof(f161,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
    | u1_pre_topc(sK2) = u1_pre_topc(sK3) ),
    inference(superposition,[],[f82,f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
      | u1_pre_topc(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f80,f69])).

fof(f80,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_pre_topc(sK2) = X1 ) ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1060,plain,
    ( r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f1059,f32])).

fof(f1059,plain,
    ( r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f826,f36])).

fof(f826,plain,
    ( r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK3))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f824,f68])).

fof(f824,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | r2_hidden(sK5(sK1,sK3),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK3))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(superposition,[],[f360,f204])).

fof(f360,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_struct_0(X12),k2_struct_0(sK0))
      | r2_hidden(sK5(sK1,X12),u1_pre_topc(sK0))
      | r2_hidden(sK4(sK1,X12),u1_pre_topc(X12))
      | m1_pre_topc(X12,sK1)
      | ~ l1_pre_topc(X12) ) ),
    inference(forward_demodulation,[],[f359,f187])).

fof(f187,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,
    ( g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f183,f58])).

fof(f183,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(superposition,[],[f100,f33])).

fof(f100,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = X1 ) ),
    inference(resolution,[],[f64,f52])).

fof(f359,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_struct_0(X12),k2_struct_0(sK0))
      | r2_hidden(sK5(sK1,X12),u1_pre_topc(sK1))
      | r2_hidden(sK4(sK1,X12),u1_pre_topc(X12))
      | m1_pre_topc(X12,sK1)
      | ~ l1_pre_topc(X12) ) ),
    inference(subsumption_resolution,[],[f340,f30])).

fof(f340,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_struct_0(X12),k2_struct_0(sK0))
      | r2_hidden(sK5(sK1,X12),u1_pre_topc(sK1))
      | r2_hidden(sK4(sK1,X12),u1_pre_topc(X12))
      | m1_pre_topc(X12,sK1)
      | ~ l1_pre_topc(X12)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f47,f235])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1058,plain,
    ( spl7_30
    | spl7_42 ),
    inference(avatar_split_clause,[],[f1057,f1049,f802])).

fof(f1057,plain,
    ( m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK0)))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f1056,f235])).

fof(f1056,plain,
    ( m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f1055,f65])).

fof(f1055,plain,
    ( r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f1054,f30])).

fof(f1054,plain,
    ( r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1053,f36])).

fof(f1053,plain,
    ( r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f837,f68])).

fof(f837,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | m1_subset_1(sK5(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f318,f235])).

fof(f318,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X9))
      | r2_hidden(sK4(X9,sK3),u1_pre_topc(sK2))
      | m1_subset_1(sK5(X9,sK3),k1_zfmisc_1(u1_struct_0(X9)))
      | m1_pre_topc(sK3,X9)
      | ~ l1_pre_topc(X9) ) ),
    inference(forward_demodulation,[],[f317,f165])).

fof(f317,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X9))
      | m1_subset_1(sK5(X9,sK3),k1_zfmisc_1(u1_struct_0(X9)))
      | r2_hidden(sK4(X9,sK3),u1_pre_topc(sK3))
      | m1_pre_topc(sK3,X9)
      | ~ l1_pre_topc(X9) ) ),
    inference(subsumption_resolution,[],[f300,f32])).

fof(f300,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X9))
      | m1_subset_1(sK5(X9,sK3),k1_zfmisc_1(u1_struct_0(X9)))
      | r2_hidden(sK4(X9,sK3),u1_pre_topc(sK3))
      | m1_pre_topc(sK3,X9)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f46,f204])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1047,plain,
    ( spl7_30
    | spl7_41 ),
    inference(avatar_split_clause,[],[f1046,f1040,f802])).

fof(f1046,plain,
    ( sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(sK1,sK3),k2_struct_0(sK2))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f1045,f30])).

fof(f1045,plain,
    ( sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(sK1,sK3),k2_struct_0(sK2))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1044,f36])).

fof(f1044,plain,
    ( sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(sK1,sK3),k2_struct_0(sK2))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f851,f68])).

fof(f851,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(sK1,sK3),k2_struct_0(sK2))
    | r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f327,f235])).

fof(f327,plain,(
    ! [X13] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X13))
      | sK4(X13,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(X13,sK3),k2_struct_0(sK2))
      | r2_hidden(sK4(X13,sK3),u1_pre_topc(sK2))
      | m1_pre_topc(sK3,X13)
      | ~ l1_pre_topc(X13) ) ),
    inference(forward_demodulation,[],[f326,f165])).

fof(f326,plain,(
    ! [X13] :
      ( sK4(X13,sK3) = k9_subset_1(k2_struct_0(sK2),sK5(X13,sK3),k2_struct_0(sK2))
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X13))
      | r2_hidden(sK4(X13,sK3),u1_pre_topc(sK3))
      | m1_pre_topc(sK3,X13)
      | ~ l1_pre_topc(X13) ) ),
    inference(forward_demodulation,[],[f325,f204])).

fof(f325,plain,(
    ! [X13] :
      ( sK4(X13,sK3) = k9_subset_1(k2_struct_0(sK3),sK5(X13,sK3),k2_struct_0(sK2))
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X13))
      | r2_hidden(sK4(X13,sK3),u1_pre_topc(sK3))
      | m1_pre_topc(sK3,X13)
      | ~ l1_pre_topc(X13) ) ),
    inference(forward_demodulation,[],[f324,f70])).

fof(f324,plain,(
    ! [X13] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X13))
      | sK4(X13,sK3) = k9_subset_1(u1_struct_0(sK3),sK5(X13,sK3),k2_struct_0(sK2))
      | r2_hidden(sK4(X13,sK3),u1_pre_topc(sK3))
      | m1_pre_topc(sK3,X13)
      | ~ l1_pre_topc(X13) ) ),
    inference(subsumption_resolution,[],[f304,f32])).

fof(f304,plain,(
    ! [X13] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X13))
      | sK4(X13,sK3) = k9_subset_1(u1_struct_0(sK3),sK5(X13,sK3),k2_struct_0(sK2))
      | r2_hidden(sK4(X13,sK3),u1_pre_topc(sK3))
      | m1_pre_topc(sK3,X13)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(X13) ) ),
    inference(superposition,[],[f48,f204])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1000,plain,(
    ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f998,f68])).

fof(f998,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f997,f204])).

fof(f997,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f996,f898])).

fof(f898,plain,
    ( sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f896,f29])).

fof(f896,plain,
    ( sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_30 ),
    inference(resolution,[],[f872,f35])).

fof(f872,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK6(X1,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f864,f804])).

fof(f804,plain,
    ( r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f802])).

fof(f864,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
      | sK4(sK1,sK3) = k9_subset_1(k2_struct_0(sK2),sK6(X1,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f741,f123])).

fof(f123,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X4,u1_pre_topc(sK2))
      | k9_subset_1(k2_struct_0(sK2),sK6(X5,sK2,X4),k2_struct_0(sK2)) = X4
      | ~ m1_pre_topc(sK2,X5)
      | ~ l1_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f118,f31])).

fof(f118,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X4,u1_pre_topc(sK2))
      | k9_subset_1(k2_struct_0(sK2),sK6(X5,sK2,X4),k2_struct_0(sK2)) = X4
      | ~ m1_pre_topc(sK2,X5)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f43,f69])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f996,plain,
    ( sK4(sK1,sK3) != k9_subset_1(k2_struct_0(sK2),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f995,f204])).

fof(f995,plain,
    ( sK4(sK1,sK3) != k9_subset_1(k2_struct_0(sK3),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f994,f70])).

fof(f994,plain,
    ( sK4(sK1,sK3) != k9_subset_1(u1_struct_0(sK3),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK2))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f993,f204])).

fof(f993,plain,
    ( sK4(sK1,sK3) != k9_subset_1(u1_struct_0(sK3),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f992,f32])).

fof(f992,plain,
    ( sK4(sK1,sK3) != k9_subset_1(u1_struct_0(sK3),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f991,f36])).

fof(f991,plain,
    ( sK4(sK1,sK3) != k9_subset_1(u1_struct_0(sK3),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK3))
    | m1_pre_topc(sK3,sK1)
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f989,f804])).

fof(f989,plain,
    ( ~ r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
    | sK4(sK1,sK3) != k9_subset_1(u1_struct_0(sK3),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(sK3))
    | m1_pre_topc(sK3,sK1)
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_30 ),
    inference(superposition,[],[f942,f165])).

fof(f942,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK4(sK1,X4),u1_pre_topc(X4))
        | k9_subset_1(u1_struct_0(X4),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(X4)) != sK4(sK1,X4)
        | m1_pre_topc(X4,sK1)
        | ~ r1_tarski(k2_struct_0(X4),k2_struct_0(sK0))
        | ~ l1_pre_topc(X4) )
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f934,f881])).

fof(f881,plain,
    ( r2_hidden(sK6(sK0,sK2,sK4(sK1,sK3)),u1_pre_topc(sK0))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f879,f29])).

fof(f879,plain,
    ( r2_hidden(sK6(sK0,sK2,sK4(sK1,sK3)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_30 ),
    inference(resolution,[],[f874,f35])).

fof(f874,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(sK2,X3)
        | r2_hidden(sK6(X3,sK2,sK4(sK1,sK3)),u1_pre_topc(X3))
        | ~ l1_pre_topc(X3) )
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f866,f804])).

fof(f866,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
      | r2_hidden(sK6(X3,sK2,sK4(sK1,sK3)),u1_pre_topc(X3))
      | ~ m1_pre_topc(sK2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f741,f125])).

fof(f125,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X8,u1_pre_topc(sK2))
      | r2_hidden(sK6(X9,sK2,X8),u1_pre_topc(X9))
      | ~ m1_pre_topc(sK2,X9)
      | ~ l1_pre_topc(X9) ) ),
    inference(subsumption_resolution,[],[f120,f31])).

fof(f120,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X8,u1_pre_topc(sK2))
      | r2_hidden(sK6(X9,sK2,X8),u1_pre_topc(X9))
      | ~ m1_pre_topc(sK2,X9)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f42,f69])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f934,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK6(sK0,sK2,sK4(sK1,sK3)),u1_pre_topc(sK0))
        | ~ r1_tarski(k2_struct_0(X4),k2_struct_0(sK0))
        | k9_subset_1(u1_struct_0(X4),sK6(sK0,sK2,sK4(sK1,sK3)),k2_struct_0(X4)) != sK4(sK1,X4)
        | m1_pre_topc(X4,sK1)
        | ~ r2_hidden(sK4(sK1,X4),u1_pre_topc(X4))
        | ~ l1_pre_topc(X4) )
    | ~ spl7_30 ),
    inference(resolution,[],[f889,f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(sK0))
      | k9_subset_1(u1_struct_0(X1),X0,k2_struct_0(X1)) != sK4(sK1,X1)
      | m1_pre_topc(X1,sK1)
      | ~ r2_hidden(sK4(sK1,X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f247,f235])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(X1),X0,k2_struct_0(X1)) != sK4(sK1,X1)
      | m1_pre_topc(X1,sK1)
      | ~ r2_hidden(sK4(sK1,X1),u1_pre_topc(X1))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(sK1))
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f246,f187])).

fof(f246,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(X1),X0,k2_struct_0(X1)) != sK4(sK1,X1)
      | ~ r2_hidden(X0,u1_pre_topc(sK1))
      | m1_pre_topc(X1,sK1)
      | ~ r2_hidden(sK4(sK1,X1),u1_pre_topc(X1))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(sK1))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f239,f30])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(X1),X0,k2_struct_0(X1)) != sK4(sK1,X1)
      | ~ r2_hidden(X0,u1_pre_topc(sK1))
      | m1_pre_topc(X1,sK1)
      | ~ r2_hidden(sK4(sK1,X1),u1_pre_topc(X1))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(sK1))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f49,f193])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | m1_pre_topc(X1,X0)
      | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f889,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK4(sK1,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f888,f58])).

fof(f888,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK4(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f886,f29])).

fof(f886,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK4(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_30 ),
    inference(resolution,[],[f873,f35])).

fof(f873,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(sK2,X2)
        | m1_subset_1(sK6(X2,sK2,sK4(sK1,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2) )
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f865,f804])).

fof(f865,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(sK1,sK3),u1_pre_topc(sK2))
      | m1_subset_1(sK6(X2,sK2,sK4(sK1,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f741,f124])).

fof(f124,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X6,u1_pre_topc(sK2))
      | m1_subset_1(sK6(X7,sK2,X6),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_pre_topc(sK2,X7)
      | ~ l1_pre_topc(X7) ) ),
    inference(subsumption_resolution,[],[f119,f31])).

fof(f119,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X6,u1_pre_topc(sK2))
      | m1_subset_1(sK6(X7,sK2,X6),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_pre_topc(sK2,X7)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f41,f69])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------

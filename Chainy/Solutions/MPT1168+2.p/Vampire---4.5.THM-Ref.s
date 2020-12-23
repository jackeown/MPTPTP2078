%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1168+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 9.16s
% Output     : Refutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 803 expanded)
%              Number of leaves         :   24 ( 339 expanded)
%              Depth                    :   30
%              Number of atoms          : 1054 (7616 expanded)
%              Number of equality atoms :   21 ( 783 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f12891,f13107,f13115,f13131,f13334,f13718,f16591])).

fof(f16591,plain,
    ( spl665_5
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(avatar_contradiction_clause,[],[f16590])).

fof(f16590,plain,
    ( $false
    | spl665_5
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(subsumption_resolution,[],[f16589,f5794])).

fof(f5794,plain,(
    m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19))) ),
    inference(cnf_transformation,[],[f4241])).

fof(f4241,plain,
    ( k3_orders_2(sK19,sK21,sK20) != k3_orders_2(sK19,sK22,sK20)
    & m1_orders_2(sK21,sK19,sK22)
    & r2_hidden(sK20,sK21)
    & m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    & m1_subset_1(sK20,u1_struct_0(sK19))
    & l1_orders_2(sK19)
    & v5_orders_2(sK19)
    & v4_orders_2(sK19)
    & v3_orders_2(sK19)
    & ~ v2_struct_0(sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21,sK22])],[f1980,f4240,f4239,f4238,f4237])).

fof(f4237,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                    & m1_orders_2(X2,X0,X3)
                    & r2_hidden(X1,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(sK19,X2,X1) != k3_orders_2(sK19,X3,X1)
                  & m1_orders_2(X2,sK19,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK19))) )
          & m1_subset_1(X1,u1_struct_0(sK19)) )
      & l1_orders_2(sK19)
      & v5_orders_2(sK19)
      & v4_orders_2(sK19)
      & v3_orders_2(sK19)
      & ~ v2_struct_0(sK19) ) ),
    introduced(choice_axiom,[])).

fof(f4238,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k3_orders_2(sK19,X2,X1) != k3_orders_2(sK19,X3,X1)
                & m1_orders_2(X2,sK19,X3)
                & r2_hidden(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK19))) )
        & m1_subset_1(X1,u1_struct_0(sK19)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k3_orders_2(sK19,X2,sK20) != k3_orders_2(sK19,X3,sK20)
              & m1_orders_2(X2,sK19,X3)
              & r2_hidden(sK20,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK19))) )
      & m1_subset_1(sK20,u1_struct_0(sK19)) ) ),
    introduced(choice_axiom,[])).

fof(f4239,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k3_orders_2(sK19,X2,sK20) != k3_orders_2(sK19,X3,sK20)
            & m1_orders_2(X2,sK19,X3)
            & r2_hidden(sK20,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK19))) )
   => ( ? [X3] :
          ( k3_orders_2(sK19,X3,sK20) != k3_orders_2(sK19,sK21,sK20)
          & m1_orders_2(sK21,sK19,X3)
          & r2_hidden(sK20,sK21)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
      & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19))) ) ),
    introduced(choice_axiom,[])).

fof(f4240,plain,
    ( ? [X3] :
        ( k3_orders_2(sK19,X3,sK20) != k3_orders_2(sK19,sK21,sK20)
        & m1_orders_2(sK21,sK19,X3)
        & r2_hidden(sK20,sK21)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
   => ( k3_orders_2(sK19,sK21,sK20) != k3_orders_2(sK19,sK22,sK20)
      & m1_orders_2(sK21,sK19,sK22)
      & r2_hidden(sK20,sK21)
      & m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19))) ) ),
    introduced(choice_axiom,[])).

fof(f1980,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1979])).

fof(f1979,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1929])).

fof(f1929,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_orders_2(X2,X0,X3)
                        & r2_hidden(X1,X2) )
                     => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1928])).

fof(f1928,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_orders_2(X2,X0,X3)
                      & r2_hidden(X1,X2) )
                   => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_orders_2)).

fof(f16589,plain,
    ( ~ m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    | spl665_5
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(subsumption_resolution,[],[f16577,f12885])).

fof(f12885,plain,
    ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20))
    | spl665_5 ),
    inference(avatar_component_clause,[],[f12884])).

fof(f12884,plain,
    ( spl665_5
  <=> r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl665_5])])).

fof(f16577,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20))
    | ~ m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(resolution,[],[f15096,f13400])).

fof(f13400,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0)
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,X0,sK20))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK19))) )
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13399,f5795])).

fof(f5795,plain,(
    m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19))) ),
    inference(cnf_transformation,[],[f4241])).

fof(f13399,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK19)))
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,X0,sK20))
        | ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0)
        | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19))) )
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13396,f5793])).

fof(f5793,plain,(
    m1_subset_1(sK20,u1_struct_0(sK19)) ),
    inference(cnf_transformation,[],[f4241])).

fof(f13396,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK19)))
        | ~ m1_subset_1(sK20,u1_struct_0(sK19))
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,X0,sK20))
        | ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0)
        | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19))) )
    | ~ spl665_6 ),
    inference(resolution,[],[f12818,f12890])).

fof(f12890,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK22,sK20))
    | ~ spl665_6 ),
    inference(avatar_component_clause,[],[f12888])).

fof(f12888,plain,
    ( spl665_6
  <=> r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK22,sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl665_6])])).

fof(f12818,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) ) ),
    inference(subsumption_resolution,[],[f12817,f8717])).

fof(f8717,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3867])).

fof(f3867,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3866])).

fof(f3866,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f12817,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19)) ) ),
    inference(subsumption_resolution,[],[f12816,f5788])).

fof(f5788,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f4241])).

fof(f12816,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12815,f5789])).

fof(f5789,plain,(
    v3_orders_2(sK19) ),
    inference(cnf_transformation,[],[f4241])).

fof(f12815,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12814,f5790])).

fof(f5790,plain,(
    v4_orders_2(sK19) ),
    inference(cnf_transformation,[],[f4241])).

fof(f12814,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12813,f5791])).

fof(f5791,plain,(
    v5_orders_2(sK19) ),
    inference(cnf_transformation,[],[f4241])).

fof(f12813,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ v5_orders_2(sK19)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12812,f5792])).

fof(f5792,plain,(
    l1_orders_2(sK19) ),
    inference(cnf_transformation,[],[f4241])).

fof(f12812,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ l1_orders_2(sK19)
      | ~ v5_orders_2(sK19)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(duplicate_literal_removal,[],[f12811])).

fof(f12811,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ r2_hidden(X0,k3_orders_2(sK19,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ l1_orders_2(sK19)
      | ~ v5_orders_2(sK19)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(resolution,[],[f12722,f6573])).

fof(f6573,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4567])).

fof(f4567,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4566])).

fof(f4566,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2410])).

fof(f2410,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2409])).

fof(f2409,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1919])).

fof(f1919,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f12722,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(sK19,X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f12721,f5788])).

fof(f12721,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK19,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12720,f5789])).

fof(f12720,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK19,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12719,f5790])).

fof(f12719,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK19,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12718,f5792])).

fof(f12718,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK19,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ l1_orders_2(sK19)
      | r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(resolution,[],[f12717,f5791])).

fof(f12717,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6575,f8717])).

fof(f6575,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4567])).

fof(f15096,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK21)
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(subsumption_resolution,[],[f15095,f5796])).

fof(f5796,plain,(
    r2_hidden(sK20,sK21) ),
    inference(cnf_transformation,[],[f4241])).

fof(f15095,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK21)
    | ~ r2_hidden(sK20,sK21)
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(subsumption_resolution,[],[f15094,f5795])).

fof(f15094,plain,
    ( ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK21)
    | ~ r2_hidden(sK20,sK21)
    | ~ spl665_6
    | ~ spl665_9 ),
    inference(subsumption_resolution,[],[f15089,f13329])).

fof(f13329,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK22)
    | ~ spl665_9 ),
    inference(avatar_component_clause,[],[f13327])).

fof(f13327,plain,
    ( spl665_9
  <=> r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl665_9])])).

fof(f15089,plain,
    ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK22)
    | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK21)
    | ~ r2_hidden(sK20,sK21)
    | ~ spl665_6 ),
    inference(resolution,[],[f13468,f5797])).

fof(f5797,plain,(
    m1_orders_2(sK21,sK19,sK22) ),
    inference(cnf_transformation,[],[f4241])).

fof(f13468,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,sK19,X0)
        | ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK19)))
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X1)
        | ~ r2_hidden(sK20,X1) )
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13467,f5793])).

fof(f13467,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0)
        | ~ m1_orders_2(X1,sK19,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK19)))
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X1)
        | ~ r2_hidden(sK20,X1)
        | ~ m1_subset_1(sK20,u1_struct_0(sK19)) )
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13464,f5795])).

fof(f13464,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0)
        | ~ m1_orders_2(X1,sK19,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK19)))
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X1)
        | ~ r2_hidden(sK20,X1)
        | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
        | ~ m1_subset_1(sK20,u1_struct_0(sK19)) )
    | ~ spl665_6 ),
    inference(resolution,[],[f12832,f12890])).

fof(f12832,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19)) ) ),
    inference(subsumption_resolution,[],[f12831,f8717])).

fof(f12831,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ m1_subset_1(X2,u1_struct_0(sK19)) ) ),
    inference(subsumption_resolution,[],[f12830,f5788])).

fof(f12830,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12829,f5789])).

fof(f12829,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12828,f5790])).

fof(f12828,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12827,f5791])).

fof(f12827,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ v5_orders_2(sK19)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12826,f5792])).

fof(f12826,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_orders_2(X1,sK19,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k3_orders_2(sK19,X4,X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ l1_orders_2(sK19)
      | ~ v5_orders_2(sK19)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(resolution,[],[f12742,f6573])).

fof(f12742,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_orders_2(sK19,X3,X2)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_orders_2(X0,sK19,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X3,X0) ) ),
    inference(subsumption_resolution,[],[f12741,f5788])).

fof(f12741,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK19,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK19,X3,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X3,X0)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12740,f5789])).

fof(f12740,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK19,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK19,X3,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X3,X0)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12739,f5790])).

fof(f12739,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK19,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK19,X3,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | r2_hidden(X3,X0)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12738,f5792])).

fof(f12738,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK19,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK19,X3,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ l1_orders_2(sK19)
      | r2_hidden(X3,X0)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(resolution,[],[f12737,f5791])).

fof(f12737,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,X4)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f12736,f7686])).

fof(f7686,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3124])).

fof(f3124,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3123])).

fof(f3123,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1881])).

fof(f1881,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f12736,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f12735,f8717])).

fof(f12735,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6576,f8717])).

fof(f6576,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2412])).

fof(f2412,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2411])).

fof(f2411,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1927])).

fof(f1927,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

fof(f13718,plain,
    ( ~ spl665_6
    | spl665_10 ),
    inference(avatar_contradiction_clause,[],[f13708])).

fof(f13708,plain,
    ( $false
    | ~ spl665_6
    | spl665_10 ),
    inference(unit_resulting_resolution,[],[f13333,f13227,f7540])).

fof(f7540,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2993])).

fof(f2993,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f13227,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13226,f5788])).

fof(f13226,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13225,f5789])).

fof(f13225,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13224,f5790])).

fof(f13224,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13223,f5791])).

fof(f13223,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13222,f5792])).

fof(f13222,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13221,f5795])).

fof(f13221,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13216,f5793])).

fof(f13216,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | ~ m1_subset_1(sK20,u1_struct_0(sK19))
    | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | ~ spl665_6 ),
    inference(resolution,[],[f13120,f8421])).

fof(f8421,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3601])).

fof(f3601,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3600])).

fof(f3600,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1877])).

fof(f1877,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f13120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_orders_2(sK19,sK22,sK20),k1_zfmisc_1(X0))
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X0) )
    | ~ spl665_6 ),
    inference(resolution,[],[f12890,f7567])).

fof(f7567,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3018])).

fof(f3018,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f13333,plain,
    ( ~ m1_subset_1(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | spl665_10 ),
    inference(avatar_component_clause,[],[f13331])).

fof(f13331,plain,
    ( spl665_10
  <=> m1_subset_1(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl665_10])])).

fof(f13334,plain,
    ( spl665_9
    | ~ spl665_10
    | ~ spl665_6 ),
    inference(avatar_split_clause,[],[f13133,f12888,f13331,f13327])).

fof(f13133,plain,
    ( ~ m1_subset_1(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK22)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13132,f5793])).

fof(f13132,plain,
    ( ~ m1_subset_1(sK20,u1_struct_0(sK19))
    | ~ m1_subset_1(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK22)
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13118,f5795])).

fof(f13118,plain,
    ( ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ m1_subset_1(sK20,u1_struct_0(sK19))
    | ~ m1_subset_1(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),u1_struct_0(sK19))
    | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),sK22)
    | ~ spl665_6 ),
    inference(resolution,[],[f12890,f12714])).

fof(f12714,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f12713,f5788])).

fof(f12713,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | r2_hidden(X0,X1)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12712,f5789])).

fof(f12712,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | r2_hidden(X0,X1)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12711,f5790])).

fof(f12711,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | r2_hidden(X0,X1)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(subsumption_resolution,[],[f12710,f5792])).

fof(f12710,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK19,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK19)))
      | ~ m1_subset_1(X2,u1_struct_0(sK19))
      | ~ m1_subset_1(X0,u1_struct_0(sK19))
      | ~ l1_orders_2(sK19)
      | r2_hidden(X0,X1)
      | ~ v4_orders_2(sK19)
      | ~ v3_orders_2(sK19)
      | v2_struct_0(sK19) ) ),
    inference(resolution,[],[f6574,f5791])).

fof(f6574,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,X3)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4567])).

fof(f13131,plain,
    ( ~ spl665_5
    | ~ spl665_6 ),
    inference(avatar_contradiction_clause,[],[f13130])).

fof(f13130,plain,
    ( $false
    | ~ spl665_5
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13129,f12886])).

fof(f12886,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20))
    | ~ spl665_5 ),
    inference(avatar_component_clause,[],[f12884])).

fof(f13129,plain,
    ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20))
    | ~ spl665_6 ),
    inference(subsumption_resolution,[],[f13117,f10120])).

fof(f10120,plain,(
    ~ sQ664_eqProxy(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)) ),
    inference(equality_proxy_replacement,[],[f5798,f10089])).

fof(f10089,plain,(
    ! [X1,X0] :
      ( sQ664_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ664_eqProxy])])).

fof(f5798,plain,(
    k3_orders_2(sK19,sK21,sK20) != k3_orders_2(sK19,sK22,sK20) ),
    inference(cnf_transformation,[],[f4241])).

fof(f13117,plain,
    ( sQ664_eqProxy(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20))
    | ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20))
    | ~ spl665_6 ),
    inference(resolution,[],[f12890,f10946])).

fof(f10946,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK418(X0,X1),X1)
      | sQ664_eqProxy(X0,X1)
      | ~ r2_hidden(sK418(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f7990,f10089])).

fof(f7990,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK418(X0,X1),X1)
      | ~ r2_hidden(sK418(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f5213])).

fof(f5213,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK418(X0,X1),X1)
          | ~ r2_hidden(sK418(X0,X1),X0) )
        & ( r2_hidden(sK418(X0,X1),X1)
          | r2_hidden(sK418(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK418])],[f5211,f5212])).

fof(f5212,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK418(X0,X1),X1)
          | ~ r2_hidden(sK418(X0,X1),X0) )
        & ( r2_hidden(sK418(X0,X1),X1)
          | r2_hidden(sK418(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f5211,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f3382])).

fof(f3382,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f13115,plain,
    ( ~ spl665_5
    | spl665_6
    | ~ spl665_7 ),
    inference(avatar_contradiction_clause,[],[f13114])).

fof(f13114,plain,
    ( $false
    | ~ spl665_5
    | spl665_6
    | ~ spl665_7 ),
    inference(subsumption_resolution,[],[f13110,f12889])).

fof(f12889,plain,
    ( ~ r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK22,sK20))
    | spl665_6 ),
    inference(avatar_component_clause,[],[f12888])).

fof(f13110,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK22,sK20))
    | ~ spl665_5
    | ~ spl665_7 ),
    inference(resolution,[],[f13071,f12895])).

fof(f12895,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_orders_2(sK19,sK21,sK20),X1)
        | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),X1) )
    | ~ spl665_5 ),
    inference(resolution,[],[f12886,f8029])).

fof(f8029,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5245])).

fof(f5245,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK428(X0,X1),X1)
          & r2_hidden(sK428(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK428])],[f5243,f5244])).

fof(f5244,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK428(X0,X1),X1)
        & r2_hidden(sK428(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f5243,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f5242])).

fof(f5242,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3389])).

fof(f3389,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f13071,plain,
    ( r1_tarski(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20))
    | ~ spl665_7 ),
    inference(avatar_component_clause,[],[f13070])).

fof(f13070,plain,
    ( spl665_7
  <=> r1_tarski(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl665_7])])).

fof(f13107,plain,(
    spl665_7 ),
    inference(avatar_contradiction_clause,[],[f13101])).

fof(f13101,plain,
    ( $false
    | spl665_7 ),
    inference(unit_resulting_resolution,[],[f5788,f5789,f5790,f5791,f5792,f5797,f5795,f13100,f6586])).

fof(f6586,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2430])).

fof(f2430,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2429])).

fof(f2429,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1924])).

fof(f1924,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f13100,plain,
    ( ~ r1_tarski(sK21,sK22)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13099,f5788])).

fof(f13099,plain,
    ( ~ r1_tarski(sK21,sK22)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13098,f5789])).

fof(f13098,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13097,f5790])).

fof(f13097,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13096,f5791])).

fof(f13096,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13095,f5792])).

fof(f13095,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13094,f5793])).

fof(f13094,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ m1_subset_1(sK20,u1_struct_0(sK19))
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13093,f5794])).

fof(f13093,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ m1_subset_1(sK20,u1_struct_0(sK19))
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(subsumption_resolution,[],[f13087,f5795])).

fof(f13087,plain,
    ( ~ r1_tarski(sK21,sK22)
    | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ m1_subset_1(sK20,u1_struct_0(sK19))
    | ~ l1_orders_2(sK19)
    | ~ v5_orders_2(sK19)
    | ~ v4_orders_2(sK19)
    | ~ v3_orders_2(sK19)
    | v2_struct_0(sK19)
    | spl665_7 ),
    inference(resolution,[],[f13072,f6580])).

fof(f6580,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
      | ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2420])).

fof(f2420,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  | ~ r1_tarski(X2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2419])).

fof(f2419,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  | ~ r1_tarski(X2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1923])).

fof(f1923,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

fof(f13072,plain,
    ( ~ r1_tarski(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20))
    | spl665_7 ),
    inference(avatar_component_clause,[],[f13070])).

fof(f12891,plain,
    ( spl665_5
    | spl665_6 ),
    inference(avatar_split_clause,[],[f12701,f12888,f12884])).

fof(f12701,plain,
    ( r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK22,sK20))
    | r2_hidden(sK418(k3_orders_2(sK19,sK21,sK20),k3_orders_2(sK19,sK22,sK20)),k3_orders_2(sK19,sK21,sK20)) ),
    inference(resolution,[],[f10947,f10120])).

fof(f10947,plain,(
    ! [X0,X1] :
      ( sQ664_eqProxy(X0,X1)
      | r2_hidden(sK418(X0,X1),X1)
      | r2_hidden(sK418(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f7989,f10089])).

fof(f7989,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK418(X0,X1),X1)
      | r2_hidden(sK418(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f5213])).
%------------------------------------------------------------------------------

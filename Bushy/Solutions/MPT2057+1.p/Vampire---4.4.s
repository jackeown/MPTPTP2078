%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t16_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 543 expanded)
%              Number of leaves         :   32 ( 197 expanded)
%              Depth                    :   16
%              Number of atoms          :  565 (5027 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f212,f219,f257,f288,f290,f340,f350,f352,f354,f369,f394,f478,f490,f656,f681,f692,f704,f742])).

fof(f742,plain,(
    ~ spl10_102 ),
    inference(avatar_contradiction_clause,[],[f741])).

fof(f741,plain,
    ( $false
    | ~ spl10_102 ),
    inference(subsumption_resolution,[],[f139,f716])).

fof(f716,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_102 ),
    inference(backward_demodulation,[],[f680,f135])).

fof(f135,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,
    ( ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
      | ~ r2_hidden(sK2,sK1) )
    & ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
      | r2_hidden(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f103,f106,f105,f104])).

fof(f104,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                  | ~ r2_hidden(X2,X1) )
                & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                  | r2_hidden(X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f105,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)
              | ~ r2_hidden(X2,sK1) )
            & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)
              | r2_hidden(X2,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
            | ~ r2_hidden(X2,X1) )
          & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
            | r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X2) )
     => ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)
          | ~ r2_hidden(sK2,X1) )
        & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)
          | r2_hidden(sK2,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | ~ r2_hidden(X2,X1) )
              & ( r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                | r2_hidden(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X2,X1)
                <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
             => ( r2_hidden(X2,X1)
              <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',t16_yellow19)).

fof(f680,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl10_102 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl10_102
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f139,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',dt_o_0_0_xboole_0)).

fof(f704,plain,
    ( spl10_1
    | ~ spl10_66 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_66 ),
    inference(subsumption_resolution,[],[f208,f695])).

fof(f695,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl10_66 ),
    inference(resolution,[],[f494,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',t64_zfmisc_1)).

fof(f494,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl10_66
  <=> r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f208,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_1
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f692,plain,
    ( spl10_32
    | ~ spl10_35
    | spl10_66
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f691,f217,f493,f316,f313])).

fof(f313,plain,
    ( spl10_32
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f316,plain,
    ( spl10_35
  <=> ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f217,plain,
    ( spl10_2
  <=> r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f691,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f689,f341])).

fof(f341,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(forward_demodulation,[],[f249,f248])).

fof(f248,plain,(
    ! [X5] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X5) = k4_xboole_0(sK1,X5) ),
    inference(resolution,[],[f134,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',redefinition_k7_subset_1)).

fof(f134,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f107])).

fof(f249,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(global_subsumption,[],[f129,f130,f131,f132,f133,f242])).

fof(f242,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f134,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(o_0_0_xboole_0))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f155,f140])).

fof(f140,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',d2_xboole_0)).

fof(f155,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',t14_yellow19)).

fof(f133,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f107])).

fof(f132,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f107])).

fof(f131,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f107])).

fof(f130,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f129,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f689,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl10_2 ),
    inference(resolution,[],[f218,f234])).

fof(f234,plain,(
    ! [X1] :
      ( ~ r1_waybel_0(sK0,X1,sK2)
      | r2_hidden(sK2,k2_yellow19(sK0,X1))
      | ~ l1_waybel_0(X1,sK0)
      | v2_struct_0(X1) ) ),
    inference(global_subsumption,[],[f129,f130,f229])).

fof(f229,plain,(
    ! [X1] :
      ( r2_hidden(sK2,k2_yellow19(sK0,X1))
      | ~ r1_waybel_0(sK0,X1,sK2)
      | ~ l1_waybel_0(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f136,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',t11_yellow19)).

fof(f136,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f107])).

fof(f218,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f217])).

fof(f681,plain,
    ( ~ spl10_1
    | spl10_102
    | spl10_3
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f676,f504,f210,f679,f207])).

fof(f210,plain,
    ( spl10_3
  <=> ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f504,plain,
    ( spl10_70
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f676,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ r2_hidden(sK2,sK1)
    | ~ spl10_3
    | ~ spl10_70 ),
    inference(resolution,[],[f668,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f668,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | ~ spl10_3
    | ~ spl10_70 ),
    inference(resolution,[],[f505,f211])).

fof(f211,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f210])).

fof(f505,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0))) )
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f504])).

fof(f656,plain,
    ( spl10_32
    | ~ spl10_35
    | spl10_70 ),
    inference(avatar_split_clause,[],[f655,f504,f316,f313])).

fof(f655,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(global_subsumption,[],[f621])).

fof(f621,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(global_subsumption,[],[f502])).

fof(f502,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(global_subsumption,[],[f130,f129,f342])).

fof(f342,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f156,f341])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f490,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f131,f226])).

fof(f226,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl10_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f478,plain,(
    spl10_47 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f134,f339])).

fof(f339,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl10_47
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f394,plain,(
    spl10_45 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f133,f336])).

fof(f336,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl10_45
  <=> ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f369,plain,(
    ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f129,f284])).

fof(f284,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl10_28
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f354,plain,(
    spl10_43 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f132,f333])).

fof(f333,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl10_43
  <=> ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f352,plain,(
    spl10_41 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f130,f344])).

fof(f344,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_41 ),
    inference(resolution,[],[f330,f147])).

fof(f147,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',dt_k2_struct_0)).

fof(f330,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl10_41
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f350,plain,
    ( ~ spl10_33
    | ~ spl10_31
    | spl10_28
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f346,f255,f283,f286,f348])).

fof(f348,plain,
    ( spl10_33
  <=> ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f286,plain,
    ( spl10_31
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f255,plain,
    ( spl10_14
  <=> ! [X0] :
        ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f346,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl10_14 ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl10_14 ),
    inference(resolution,[],[f256,f147])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f255])).

fof(f340,plain,
    ( spl10_28
    | ~ spl10_31
    | spl10_12
    | ~ spl10_41
    | spl10_6
    | ~ spl10_43
    | ~ spl10_45
    | ~ spl10_47
    | spl10_35 ),
    inference(avatar_split_clause,[],[f327,f316,f338,f335,f332,f225,f329,f252,f286,f283])).

fof(f252,plain,
    ( spl10_12
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f327,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_35 ),
    inference(resolution,[],[f317,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',dt_k3_yellow19)).

fof(f317,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f316])).

fof(f290,plain,(
    spl10_31 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f130,f287])).

fof(f287,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f286])).

fof(f288,plain,
    ( spl10_28
    | ~ spl10_31
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f279,f252,f286,f283])).

fof(f279,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_12 ),
    inference(resolution,[],[f253,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t16_yellow19.p',fc5_struct_0)).

fof(f253,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f252])).

fof(f257,plain,
    ( spl10_12
    | spl10_14 ),
    inference(avatar_split_clause,[],[f250,f255,f252])).

fof(f250,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f131,f132,f133,f243])).

fof(f243,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f134,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f219,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f137,f217,f214])).

fof(f214,plain,
    ( spl10_0
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f137,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f107])).

fof(f212,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f138,f210,f207])).

fof(f138,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f107])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t50_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  177 (1781 expanded)
%              Number of leaves         :   46 ( 727 expanded)
%              Depth                    :   18
%              Number of atoms          : 1098 (31625 expanded)
%              Number of equality atoms :   53 ( 322 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f202,f206,f210,f214,f218,f222,f226,f237,f322,f404,f430,f487,f506,f578,f632,f640,f644,f648,f656,f663,f672,f705,f732,f786])).

fof(f786,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_77
    | spl18_18
    | ~ spl18_120 ),
    inference(avatar_split_clause,[],[f782,f589,f235,f784,f459,f291,f288])).

fof(f288,plain,
    ( spl18_30
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_30])])).

fof(f291,plain,
    ( spl18_33
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_33])])).

fof(f459,plain,
    ( spl18_73
  <=> ~ m4_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_73])])).

fof(f784,plain,
    ( spl18_77
  <=> ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_77])])).

fof(f235,plain,
    ( spl18_18
  <=> ! [X5,X6] :
        ( r1_waybel_0(sK0,X6,sK2)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK2)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK0)
        | ~ r2_hidden(k4_tarski(X6,X5),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_18])])).

fof(f589,plain,
    ( spl18_120
  <=> sK2 = sK14(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_120])])).

fof(f782,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK2)
        | r1_waybel_0(sK0,X0,sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
        | ~ m4_yellow_6(sK1,sK0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_120 ),
    inference(forward_demodulation,[],[f781,f590])).

fof(f590,plain,
    ( sK2 = sK14(sK2,sK0,sK1)
    | ~ spl18_120 ),
    inference(avatar_component_clause,[],[f589])).

fof(f781,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(sK0,X0,sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ r2_hidden(X1,sK14(sK2,sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
        | ~ m4_yellow_6(sK1,sK0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_120 ),
    inference(superposition,[],[f164,f590])).

fof(f164,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r1_waybel_0(X1,X8,sK14(X0,X1,X2))
      | ~ r2_hidden(k4_tarski(X8,X7),X2)
      | ~ l1_waybel_0(X8,X1)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ r2_hidden(X7,sK14(X0,X1,X2))
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
          | ! [X3] :
              ( ( ~ r1_waybel_0(X1,sK13(X1,X2,X3),X3)
                & r2_hidden(k4_tarski(sK13(X1,X2,X3),sK12(X1,X2,X3)),X2)
                & l1_waybel_0(sK13(X1,X2,X3),X1)
                & v7_waybel_0(sK13(X1,X2,X3))
                & v4_orders_2(sK13(X1,X2,X3))
                & ~ v2_struct_0(sK13(X1,X2,X3))
                & r2_hidden(sK12(X1,X2,X3),X3)
                & m1_subset_1(sK12(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( ! [X7] :
                ( ! [X8] :
                    ( r1_waybel_0(X1,X8,sK14(X0,X1,X2))
                    | ~ r2_hidden(k4_tarski(X8,X7),X2)
                    | ~ l1_waybel_0(X8,X1)
                    | ~ v7_waybel_0(X8)
                    | ~ v4_orders_2(X8)
                    | v2_struct_0(X8) )
                | ~ r2_hidden(X7,sK14(X0,X1,X2))
                | ~ m1_subset_1(X7,u1_struct_0(X1)) )
            & sK14(X0,X1,X2) = X0
            & m1_subset_1(sK14(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f99,f102,f101,f100])).

fof(f100,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_waybel_0(X1,X5,X3)
              & r2_hidden(k4_tarski(X5,X4),X2)
              & l1_waybel_0(X5,X1)
              & v7_waybel_0(X5)
              & v4_orders_2(X5)
              & ~ v2_struct_0(X5) )
          & r2_hidden(X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ~ r1_waybel_0(X1,X5,X3)
            & r2_hidden(k4_tarski(X5,sK12(X1,X2,X3)),X2)
            & l1_waybel_0(X5,X1)
            & v7_waybel_0(X5)
            & v4_orders_2(X5)
            & ~ v2_struct_0(X5) )
        & r2_hidden(sK12(X1,X2,X3),X3)
        & m1_subset_1(sK12(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X5] :
          ( ~ r1_waybel_0(X1,X5,X3)
          & r2_hidden(k4_tarski(X5,X4),X2)
          & l1_waybel_0(X5,X1)
          & v7_waybel_0(X5)
          & v4_orders_2(X5)
          & ~ v2_struct_0(X5) )
     => ( ~ r1_waybel_0(X1,sK13(X1,X2,X3),X3)
        & r2_hidden(k4_tarski(sK13(X1,X2,X3),X4),X2)
        & l1_waybel_0(sK13(X1,X2,X3),X1)
        & v7_waybel_0(sK13(X1,X2,X3))
        & v4_orders_2(sK13(X1,X2,X3))
        & ~ v2_struct_0(sK13(X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( r1_waybel_0(X1,X8,X6)
                  | ~ r2_hidden(k4_tarski(X8,X7),X2)
                  | ~ l1_waybel_0(X8,X1)
                  | ~ v7_waybel_0(X8)
                  | ~ v4_orders_2(X8)
                  | v2_struct_0(X8) )
              | ~ r2_hidden(X7,X6)
              | ~ m1_subset_1(X7,u1_struct_0(X1)) )
          & X0 = X6
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X7] :
            ( ! [X8] :
                ( r1_waybel_0(X1,X8,sK14(X0,X1,X2))
                | ~ r2_hidden(k4_tarski(X8,X7),X2)
                | ~ l1_waybel_0(X8,X1)
                | ~ v7_waybel_0(X8)
                | ~ v4_orders_2(X8)
                | v2_struct_0(X8) )
            | ~ r2_hidden(X7,sK14(X0,X1,X2))
            | ~ m1_subset_1(X7,u1_struct_0(X1)) )
        & sK14(X0,X1,X2) = X0
        & m1_subset_1(sK14(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_waybel_0(X1,X5,X3)
                      & r2_hidden(k4_tarski(X5,X4),X2)
                      & l1_waybel_0(X5,X1)
                      & v7_waybel_0(X5)
                      & v4_orders_2(X5)
                      & ~ v2_struct_0(X5) )
                  & r2_hidden(X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( r1_waybel_0(X1,X8,X6)
                      | ~ r2_hidden(k4_tarski(X8,X7),X2)
                      | ~ l1_waybel_0(X8,X1)
                      | ~ v7_waybel_0(X8)
                      | ~ v4_orders_2(X8)
                      | v2_struct_0(X8) )
                  | ~ r2_hidden(X7,X6)
                  | ~ m1_subset_1(X7,u1_struct_0(X1)) )
              & X0 = X6
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_waybel_0(X1,X5,X3)
                      & r2_hidden(k4_tarski(X5,X4),X2)
                      & l1_waybel_0(X5,X1)
                      & v7_waybel_0(X5)
                      & v4_orders_2(X5)
                      & ~ v2_struct_0(X5) )
                  & r2_hidden(X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( r1_waybel_0(X1,X5,X3)
                      | ~ r2_hidden(k4_tarski(X5,X4),X2)
                      | ~ l1_waybel_0(X5,X1)
                      | ~ v7_waybel_0(X5)
                      | ~ v4_orders_2(X5)
                      | v2_struct_0(X5) )
                  | ~ r2_hidden(X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m4_yellow_6(X2,X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X3)
                 => ! [X5] :
                      ( ( l1_waybel_0(X5,X1)
                        & v7_waybel_0(X5)
                        & v4_orders_2(X5)
                        & ~ v2_struct_0(X5) )
                     => ( r2_hidden(k4_tarski(X5,X4),X2)
                       => r1_waybel_0(X1,X5,X3) ) ) ) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',fraenkel_a_2_1_yellow_6)).

fof(f732,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | spl18_120
    | ~ spl18_76 ),
    inference(avatar_split_clause,[],[f727,f465,f589,f459,f291,f288])).

fof(f465,plain,
    ( spl18_76
  <=> r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_76])])).

fof(f727,plain,
    ( sK2 = sK14(sK2,sK0,sK1)
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_76 ),
    inference(resolution,[],[f466,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | sK14(X0,X1,X2) = X0
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f466,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl18_76 ),
    inference(avatar_component_clause,[],[f465])).

fof(f705,plain,
    ( spl18_2
    | ~ spl18_7
    | ~ spl18_9
    | ~ spl18_11
    | spl18_12
    | ~ spl18_15
    | ~ spl18_4
    | ~ spl18_18 ),
    inference(avatar_split_clause,[],[f683,f235,f204,f703,f700,f697,f694,f691,f688])).

fof(f688,plain,
    ( spl18_2
  <=> r1_waybel_0(sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f691,plain,
    ( spl18_7
  <=> ~ l1_waybel_0(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f694,plain,
    ( spl18_9
  <=> ~ v7_waybel_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f697,plain,
    ( spl18_11
  <=> ~ v4_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f700,plain,
    ( spl18_12
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f703,plain,
    ( spl18_15
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_15])])).

fof(f204,plain,
    ( spl18_4
  <=> r2_hidden(k4_tarski(sK4,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f683,plain,
    ( ~ r2_hidden(sK3,sK2)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4)
    | ~ l1_waybel_0(sK4,sK0)
    | r1_waybel_0(sK0,sK4,sK2)
    | ~ spl18_4
    | ~ spl18_18 ),
    inference(resolution,[],[f205,f554])).

fof(f554,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(X6,X5),sK1)
        | ~ r2_hidden(X5,sK2)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK0)
        | r1_waybel_0(sK0,X6,sK2) )
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f236,f492])).

fof(f492,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f245,f251])).

fof(f251,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | m1_subset_1(X1,u1_struct_0(k13_yellow_6(sK0,sK1))) ) ),
    inference(resolution,[],[f114,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',t4_subset)).

fof(f114,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( ( ( ~ r1_waybel_0(sK0,sK4,sK2)
        & r2_hidden(k4_tarski(sK4,sK3),sK1)
        & l1_waybel_0(sK4,sK0)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4)
        & r2_hidden(sK3,sK2)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) )
    & ( ! [X5] :
          ( ! [X6] :
              ( r1_waybel_0(sK0,X6,sK2)
              | ~ r2_hidden(k4_tarski(X6,X5),sK1)
              | ~ l1_waybel_0(X6,sK0)
              | ~ v7_waybel_0(X6)
              | ~ v4_orders_2(X6)
              | v2_struct_0(X6) )
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
      | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK0,sK1))))
    & m4_yellow_6(sK1,sK0)
    & v8_yellow_6(sK1,sK0)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f73,f78,f77,f76,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r1_waybel_0(X0,X4,X2)
                          & r2_hidden(k4_tarski(X4,X3),X1)
                          & l1_waybel_0(X4,X0)
                          & v7_waybel_0(X4)
                          & v4_orders_2(X4)
                          & ~ v2_struct_0(X4) )
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
                & ( ! [X5] :
                      ( ! [X6] :
                          ( r1_waybel_0(X0,X6,X2)
                          | ~ r2_hidden(k4_tarski(X6,X5),X1)
                          | ~ l1_waybel_0(X6,X0)
                          | ~ v7_waybel_0(X6)
                          | ~ v4_orders_2(X6)
                          | v2_struct_0(X6) )
                      | ~ r2_hidden(X5,X2)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
            & m4_yellow_6(X1,X0)
            & v8_yellow_6(X1,X0) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(sK0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,sK0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(sK0,X1)) )
              & ( ! [X5] :
                    ( ! [X6] :
                        ( r1_waybel_0(sK0,X6,X2)
                        | ~ r2_hidden(k4_tarski(X6,X5),X1)
                        | ~ l1_waybel_0(X6,sK0)
                        | ~ v7_waybel_0(X6)
                        | ~ v4_orders_2(X6)
                        | v2_struct_0(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | v3_pre_topc(X2,k13_yellow_6(sK0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK0,X1)))) )
          & m4_yellow_6(X1,sK0)
          & v8_yellow_6(X1,sK0) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X5] :
                    ( ! [X6] :
                        ( r1_waybel_0(X0,X6,X2)
                        | ~ r2_hidden(k4_tarski(X6,X5),X1)
                        | ~ l1_waybel_0(X6,X0)
                        | ~ v7_waybel_0(X6)
                        | ~ v4_orders_2(X6)
                        | v2_struct_0(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0)
          & v8_yellow_6(X1,X0) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_waybel_0(X0,X4,X2)
                      & r2_hidden(k4_tarski(X4,X3),sK1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  & r2_hidden(X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X2,k13_yellow_6(X0,sK1)) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( r1_waybel_0(X0,X6,X2)
                      | ~ r2_hidden(k4_tarski(X6,X5),sK1)
                      | ~ l1_waybel_0(X6,X0)
                      | ~ v7_waybel_0(X6)
                      | ~ v4_orders_2(X6)
                      | v2_struct_0(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | v3_pre_topc(X2,k13_yellow_6(X0,sK1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,sK1)))) )
        & m4_yellow_6(sK1,X0)
        & v8_yellow_6(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_waybel_0(X0,X4,X2)
                    & r2_hidden(k4_tarski(X4,X3),X1)
                    & l1_waybel_0(X4,X0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                & r2_hidden(X3,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
          & ( ! [X5] :
                ( ! [X6] :
                    ( r1_waybel_0(X0,X6,X2)
                    | ~ r2_hidden(k4_tarski(X6,X5),X1)
                    | ~ l1_waybel_0(X6,X0)
                    | ~ v7_waybel_0(X6)
                    | ~ v4_orders_2(X6)
                    | v2_struct_0(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
     => ( ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_waybel_0(X0,X4,sK2)
                  & r2_hidden(k4_tarski(X4,X3),X1)
                  & l1_waybel_0(X4,X0)
                  & v7_waybel_0(X4)
                  & v4_orders_2(X4)
                  & ~ v2_struct_0(X4) )
              & r2_hidden(X3,sK2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK2,k13_yellow_6(X0,X1)) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r1_waybel_0(X0,X6,sK2)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1)
                  | ~ l1_waybel_0(X6,X0)
                  | ~ v7_waybel_0(X6)
                  | ~ v4_orders_2(X6)
                  | v2_struct_0(X6) )
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | v3_pre_topc(sK2,k13_yellow_6(X0,X1)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_waybel_0(X0,X4,X2)
              & r2_hidden(k4_tarski(X4,X3),X1)
              & l1_waybel_0(X4,X0)
              & v7_waybel_0(X4)
              & v4_orders_2(X4)
              & ~ v2_struct_0(X4) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ~ r1_waybel_0(X0,X4,X2)
            & r2_hidden(k4_tarski(X4,sK3),X1)
            & l1_waybel_0(X4,X0)
            & v7_waybel_0(X4)
            & v4_orders_2(X4)
            & ~ v2_struct_0(X4) )
        & r2_hidden(sK3,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X4,X2)
          & r2_hidden(k4_tarski(X4,X3),X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( ~ r1_waybel_0(X0,sK4,X2)
        & r2_hidden(k4_tarski(sK4,X3),X1)
        & l1_waybel_0(sK4,X0)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X5] :
                    ( ! [X6] :
                        ( r1_waybel_0(X0,X6,X2)
                        | ~ r2_hidden(k4_tarski(X6,X5),X1)
                        | ~ l1_waybel_0(X6,X0)
                        | ~ v7_waybel_0(X6)
                        | ~ v4_orders_2(X6)
                        | v2_struct_0(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0)
          & v8_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0)
          & v8_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0)
          & v8_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <~> ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0)
          & v8_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <~> ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0)
          & v8_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m4_yellow_6(X1,X0)
              & v8_yellow_6(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
               => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => ! [X4] :
                            ( ( l1_waybel_0(X4,X0)
                              & v7_waybel_0(X4)
                              & v4_orders_2(X4)
                              & ~ v2_struct_0(X4) )
                           => ( r2_hidden(k4_tarski(X4,X3),X1)
                             => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m4_yellow_6(X1,X0)
            & v8_yellow_6(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
             => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                     => ! [X4] :
                          ( ( l1_waybel_0(X4,X0)
                            & v7_waybel_0(X4)
                            & v4_orders_2(X4)
                            & ~ v2_struct_0(X4) )
                         => ( r2_hidden(k4_tarski(X4,X3),X1)
                           => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',t50_yellow_6)).

fof(f245,plain,(
    u1_struct_0(sK0) = u1_struct_0(k13_yellow_6(sK0,sK1)) ),
    inference(global_subsumption,[],[f110,f111,f113,f241,f242])).

fof(f242,plain,
    ( ~ l1_pre_topc(k13_yellow_6(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k13_yellow_6(sK0,sK1))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f240,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ l1_pre_topc(k13_yellow_6(X0,X1))
      | u1_struct_0(X0) = u1_struct_0(k13_yellow_6(X0,X1))
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(X2)
      | k13_yellow_6(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k13_yellow_6(X0,X1) = X2
                  | u1_pre_topc(X2) != a_2_1_yellow_6(X0,X1)
                  | u1_struct_0(X0) != u1_struct_0(X2) )
                & ( ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                    & u1_struct_0(X0) = u1_struct_0(X2) )
                  | k13_yellow_6(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k13_yellow_6(X0,X1) = X2
                  | u1_pre_topc(X2) != a_2_1_yellow_6(X0,X1)
                  | u1_struct_0(X0) != u1_struct_0(X2) )
                & ( ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                    & u1_struct_0(X0) = u1_struct_0(X2) )
                  | k13_yellow_6(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X0) = u1_struct_0(X2) ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X0) = u1_struct_0(X2) ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m4_yellow_6(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X0) = u1_struct_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',d27_yellow_6)).

fof(f240,plain,(
    v1_pre_topc(k13_yellow_6(sK0,sK1)) ),
    inference(global_subsumption,[],[f110,f111,f238])).

fof(f238,plain,
    ( v1_pre_topc(k13_yellow_6(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f113,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m4_yellow_6(X1,X0)
      | v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) )
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) )
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m4_yellow_6(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',dt_k13_yellow_6)).

fof(f241,plain,(
    l1_pre_topc(k13_yellow_6(sK0,sK1)) ),
    inference(global_subsumption,[],[f110,f111,f239])).

fof(f239,plain,
    ( l1_pre_topc(k13_yellow_6(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f113,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m4_yellow_6(X1,X0)
      | l1_pre_topc(k13_yellow_6(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,(
    m4_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f111,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f110,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f236,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(X6,X5),sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK2)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK0)
        | r1_waybel_0(sK0,X6,sK2) )
    | ~ spl18_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK1)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f204])).

fof(f672,plain,
    ( ~ spl18_1
    | spl18_76 ),
    inference(avatar_split_clause,[],[f671,f465,f197])).

fof(f197,plain,
    ( spl18_1
  <=> ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f671,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(global_subsumption,[],[f241,f670])).

fof(f670,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(k13_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f248,f246])).

fof(f246,plain,(
    u1_pre_topc(k13_yellow_6(sK0,sK1)) = a_2_1_yellow_6(sK0,sK1) ),
    inference(global_subsumption,[],[f110,f111,f113,f241,f243])).

fof(f243,plain,
    ( ~ l1_pre_topc(k13_yellow_6(sK0,sK1))
    | u1_pre_topc(k13_yellow_6(sK0,sK1)) = a_2_1_yellow_6(sK0,sK1)
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f240,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ l1_pre_topc(k13_yellow_6(X0,X1))
      | u1_pre_topc(k13_yellow_6(X0,X1)) = a_2_1_yellow_6(X0,X1)
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
      | k13_yellow_6(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f248,plain,
    ( ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | r2_hidden(sK2,u1_pre_topc(k13_yellow_6(sK0,sK1)))
    | ~ l1_pre_topc(k13_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f114,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',d5_pre_topc)).

fof(f663,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_75
    | spl18_76
    | spl18_89 ),
    inference(avatar_split_clause,[],[f658,f483,f465,f462,f459,f291,f288])).

fof(f462,plain,
    ( spl18_75
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_75])])).

fof(f483,plain,
    ( spl18_89
  <=> ~ r2_hidden(sK12(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_89])])).

fof(f658,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_89 ),
    inference(resolution,[],[f484,f194])).

fof(f194,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK12(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | r2_hidden(sK12(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f484,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,sK2),sK2)
    | ~ spl18_89 ),
    inference(avatar_component_clause,[],[f483])).

fof(f656,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_75
    | spl18_76
    | ~ spl18_81
    | ~ spl18_83
    | ~ spl18_85
    | spl18_86
    | ~ spl18_89
    | ~ spl18_18 ),
    inference(avatar_split_clause,[],[f593,f235,f483,f480,f477,f474,f471,f465,f462,f459,f291,f288])).

fof(f471,plain,
    ( spl18_81
  <=> ~ l1_waybel_0(sK13(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_81])])).

fof(f474,plain,
    ( spl18_83
  <=> ~ v7_waybel_0(sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_83])])).

fof(f477,plain,
    ( spl18_85
  <=> ~ v4_orders_2(sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_85])])).

fof(f480,plain,
    ( spl18_86
  <=> v2_struct_0(sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_86])])).

fof(f593,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK13(sK0,sK1,sK2))
    | ~ v4_orders_2(sK13(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK13(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK13(sK0,sK1,sK2),sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_18 ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK13(sK0,sK1,sK2))
    | ~ v4_orders_2(sK13(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK13(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK13(sK0,sK1,sK2),sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_18 ),
    inference(resolution,[],[f556,f188])).

fof(f188,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_waybel_0(X1,sK13(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | ~ r1_waybel_0(X1,sK13(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f556,plain,
    ( ! [X2,X3] :
        ( r1_waybel_0(sK0,sK13(X2,sK1,X3),sK2)
        | ~ r2_hidden(sK12(X2,sK1,X3),sK2)
        | v2_struct_0(sK13(X2,sK1,X3))
        | ~ v4_orders_2(sK13(X2,sK1,X3))
        | ~ v7_waybel_0(sK13(X2,sK1,X3))
        | ~ l1_waybel_0(sK13(X2,sK1,X3),sK0)
        | r2_hidden(X3,a_2_1_yellow_6(X2,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m4_yellow_6(sK1,X2)
        | ~ l1_struct_0(X2)
        | v2_struct_0(X2) )
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f266,f492])).

fof(f266,plain,
    ( ! [X2,X3] :
        ( r1_waybel_0(sK0,sK13(X2,sK1,X3),sK2)
        | ~ r2_hidden(sK12(X2,sK1,X3),sK2)
        | v2_struct_0(sK13(X2,sK1,X3))
        | ~ v4_orders_2(sK13(X2,sK1,X3))
        | ~ v7_waybel_0(sK13(X2,sK1,X3))
        | ~ l1_waybel_0(sK13(X2,sK1,X3),sK0)
        | ~ m1_subset_1(sK12(X2,sK1,X3),u1_struct_0(sK0))
        | r2_hidden(X3,a_2_1_yellow_6(X2,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m4_yellow_6(sK1,X2)
        | ~ l1_struct_0(X2)
        | v2_struct_0(X2) )
    | ~ spl18_18 ),
    inference(resolution,[],[f236,f189])).

fof(f189,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(sK13(X1,X2,X3),sK12(X1,X2,X3)),X2)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f171])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | r2_hidden(k4_tarski(sK13(X1,X2,X3),sK12(X1,X2,X3)),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f648,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_75
    | spl18_82
    | spl18_21 ),
    inference(avatar_split_clause,[],[f630,f254,f646,f462,f459,f291,f288])).

fof(f646,plain,
    ( spl18_82
  <=> v7_waybel_0(sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_82])])).

fof(f254,plain,
    ( spl18_21
  <=> ~ r2_hidden(sK2,u1_pre_topc(k13_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_21])])).

fof(f630,plain,
    ( v7_waybel_0(sK13(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_21 ),
    inference(resolution,[],[f619,f191])).

fof(f191,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | v7_waybel_0(sK13(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f169])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | v7_waybel_0(sK13(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f619,plain,
    ( ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl18_21 ),
    inference(backward_demodulation,[],[f246,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(k13_yellow_6(sK0,sK1)))
    | ~ spl18_21 ),
    inference(avatar_component_clause,[],[f254])).

fof(f644,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_75
    | spl18_84
    | spl18_21 ),
    inference(avatar_split_clause,[],[f629,f254,f642,f462,f459,f291,f288])).

fof(f642,plain,
    ( spl18_84
  <=> v4_orders_2(sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_84])])).

fof(f629,plain,
    ( v4_orders_2(sK13(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_21 ),
    inference(resolution,[],[f619,f192])).

fof(f192,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | v4_orders_2(sK13(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | v4_orders_2(sK13(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f640,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_75
    | ~ spl18_87
    | spl18_21 ),
    inference(avatar_split_clause,[],[f628,f254,f638,f462,f459,f291,f288])).

fof(f638,plain,
    ( spl18_87
  <=> ~ v2_struct_0(sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_87])])).

fof(f628,plain,
    ( ~ v2_struct_0(sK13(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_21 ),
    inference(resolution,[],[f619,f193])).

fof(f193,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | ~ v2_struct_0(sK13(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | ~ v2_struct_0(sK13(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f632,plain,
    ( spl18_21
    | ~ spl18_76 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | ~ spl18_21
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f466,f619])).

fof(f578,plain,
    ( spl18_30
    | ~ spl18_33
    | ~ spl18_73
    | ~ spl18_75
    | spl18_76
    | spl18_81 ),
    inference(avatar_split_clause,[],[f577,f471,f465,f462,f459,f291,f288])).

fof(f577,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_81 ),
    inference(resolution,[],[f472,f190])).

fof(f190,plain,(
    ! [X2,X3,X1] :
      ( l1_waybel_0(sK13(X1,X2,X3),X1)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      | l1_waybel_0(sK13(X1,X2,X3),X1)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f472,plain,
    ( ~ l1_waybel_0(sK13(sK0,sK1,sK2),sK0)
    | ~ spl18_81 ),
    inference(avatar_component_clause,[],[f471])).

fof(f506,plain,(
    spl18_75 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl18_75 ),
    inference(subsumption_resolution,[],[f463,f493])).

fof(f493,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f245,f114])).

fof(f463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl18_75 ),
    inference(avatar_component_clause,[],[f462])).

fof(f487,plain,(
    spl18_73 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f113,f460])).

fof(f460,plain,
    ( ~ m4_yellow_6(sK1,sK0)
    | ~ spl18_73 ),
    inference(avatar_component_clause,[],[f459])).

fof(f430,plain,
    ( spl18_0
    | ~ spl18_21 ),
    inference(avatar_split_clause,[],[f429,f254,f232])).

fof(f232,plain,
    ( spl18_0
  <=> v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_0])])).

fof(f429,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(k13_yellow_6(sK0,sK1)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(global_subsumption,[],[f241,f426])).

fof(f426,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(k13_yellow_6(sK0,sK1)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(k13_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f114,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f404,plain,(
    ~ spl18_30 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl18_30 ),
    inference(subsumption_resolution,[],[f110,f289])).

fof(f289,plain,
    ( v2_struct_0(sK0)
    | ~ spl18_30 ),
    inference(avatar_component_clause,[],[f288])).

fof(f322,plain,(
    spl18_33 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl18_33 ),
    inference(subsumption_resolution,[],[f111,f292])).

fof(f292,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl18_33 ),
    inference(avatar_component_clause,[],[f291])).

fof(f237,plain,
    ( spl18_0
    | spl18_18 ),
    inference(avatar_split_clause,[],[f115,f235,f232])).

fof(f115,plain,(
    ! [X6,X5] :
      ( r1_waybel_0(sK0,X6,sK2)
      | ~ r2_hidden(k4_tarski(X6,X5),sK1)
      | ~ l1_waybel_0(X6,sK0)
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | v2_struct_0(X6)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f226,plain,
    ( ~ spl18_1
    | spl18_14 ),
    inference(avatar_split_clause,[],[f117,f224,f197])).

fof(f224,plain,
    ( spl18_14
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_14])])).

fof(f117,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f222,plain,
    ( ~ spl18_1
    | ~ spl18_13 ),
    inference(avatar_split_clause,[],[f118,f220,f197])).

fof(f220,plain,
    ( spl18_13
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).

fof(f118,plain,
    ( ~ v2_struct_0(sK4)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f218,plain,
    ( ~ spl18_1
    | spl18_10 ),
    inference(avatar_split_clause,[],[f119,f216,f197])).

fof(f216,plain,
    ( spl18_10
  <=> v4_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f119,plain,
    ( v4_orders_2(sK4)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f214,plain,
    ( ~ spl18_1
    | spl18_8 ),
    inference(avatar_split_clause,[],[f120,f212,f197])).

fof(f212,plain,
    ( spl18_8
  <=> v7_waybel_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f120,plain,
    ( v7_waybel_0(sK4)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f210,plain,
    ( ~ spl18_1
    | spl18_6 ),
    inference(avatar_split_clause,[],[f121,f208,f197])).

fof(f208,plain,
    ( spl18_6
  <=> l1_waybel_0(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f121,plain,
    ( l1_waybel_0(sK4,sK0)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f206,plain,
    ( ~ spl18_1
    | spl18_4 ),
    inference(avatar_split_clause,[],[f122,f204,f197])).

fof(f122,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK1)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f202,plain,
    ( ~ spl18_1
    | ~ spl18_3 ),
    inference(avatar_split_clause,[],[f123,f200,f197])).

fof(f200,plain,
    ( spl18_3
  <=> ~ r1_waybel_0(sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f123,plain,
    ( ~ r1_waybel_0(sK0,sK4,sK2)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).
%------------------------------------------------------------------------------

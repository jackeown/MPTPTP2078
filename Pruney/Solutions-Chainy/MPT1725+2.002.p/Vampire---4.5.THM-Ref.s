%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:07 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  448 (2932 expanded)
%              Number of leaves         :   37 (1256 expanded)
%              Depth                    :   53
%              Number of atoms          : 2899 (44957 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f80,f91,f113,f166,f233,f383,f434,f536,f601,f696,f912,f1023,f1228,f1266,f1316,f1573,f1792,f1804,f1812,f1939,f2111,f2121,f2143,f2151,f2310])).

fof(f2310,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(avatar_contradiction_clause,[],[f2309])).

fof(f2309,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2308,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
          | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
        & m1_pre_topc(sK2,sK3) )
      | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
          | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                        & m1_pre_topc(X2,X3) )
                      | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                      | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                    & m1_pre_topc(X2,X3) )
                  | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                      | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
                    & m1_pre_topc(X1,X3) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2)
                    | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2) )
                  & m1_pre_topc(X2,X3) )
                | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1)
                    | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1) )
                  & m1_pre_topc(sK1,X3) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2)
                  | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2) )
                & m1_pre_topc(X2,X3) )
              | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1)
                  | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1) )
                & m1_pre_topc(sK1,X3) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2)
                | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2) )
              & m1_pre_topc(sK2,X3) )
            | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1)
                | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1) )
              & m1_pre_topc(sK1,X3) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2)
              | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2) )
            & m1_pre_topc(sK2,X3) )
          | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1)
              | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1) )
            & m1_pre_topc(sK1,X3) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
            | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
          & m1_pre_topc(sK2,sK3) )
        | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
            | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
          & m1_pre_topc(sK1,sK3) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                        & ( m1_pre_topc(X1,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).

fof(f2308,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2307,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f2307,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2306,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f2306,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2305,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f2305,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2304,f37])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f2304,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2303,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2303,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2302,f39])).

fof(f39,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f2302,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2301,f42])).

fof(f42,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2301,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(resolution,[],[f2249,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f2249,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | spl4_52
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2248,f2105])).

fof(f2105,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f2104,plain,
    ( spl4_52
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f2248,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f2247,f2109])).

fof(f2109,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f2108])).

fof(f2108,plain,
    ( spl4_53
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f2247,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f2246,f38])).

fof(f2246,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f2237,f39])).

fof(f2237,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(resolution,[],[f2216,f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f235,f33])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f35])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f2216,plain,
    ( r1_tsep_1(sK2,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f2215,f892])).

fof(f892,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f891])).

fof(f891,plain,
    ( spl4_41
  <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f2215,plain,
    ( r1_tsep_1(sK2,k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f2208,f101])).

fof(f101,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f2208,plain,
    ( r1_tsep_1(sK2,k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f1555,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f1555,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1554,f38])).

fof(f1554,plain,
    ( v2_struct_0(sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1553,f39])).

fof(f1553,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1544,f42])).

fof(f1544,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f1542,f69])).

fof(f69,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_2
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1542,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1541,f33])).

fof(f1541,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1540,f35])).

fof(f1540,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1539,f36])).

fof(f1539,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1538,f37])).

fof(f1538,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(duplicate_literal_removal,[],[f1535])).

fof(f1535,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f1453,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f1453,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1452,f33])).

fof(f1452,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1451,f35])).

fof(f1451,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1450,f36])).

fof(f1450,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1449,f37])).

fof(f1449,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(duplicate_literal_removal,[],[f1448])).

fof(f1448,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f1401,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1401,plain,
    ( ! [X0] :
        ( v2_struct_0(k2_tsep_1(sK0,sK1,X0))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1400,f36])).

fof(f1400,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1399,f37])).

fof(f1399,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1398,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1398,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1393,f41])).

fof(f41,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1393,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f1214,f688])).

fof(f688,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(sK0,X2,X0),k2_tsep_1(sK0,X2,X1))
      | r1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f687,f33])).

fof(f687,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | r1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | m1_pre_topc(k2_tsep_1(sK0,X2,X0),k2_tsep_1(sK0,X2,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f686,f35])).

fof(f686,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | r1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(k2_tsep_1(sK0,X2,X0),k2_tsep_1(sK0,X2,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f34])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f1214,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2) )
    | ~ spl4_3
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1213,f219])).

fof(f219,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_18
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1213,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2) )
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1212,f223])).

fof(f223,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl4_19
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1212,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f1211,f38])).

fof(f1211,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f1201,f39])).

fof(f1201,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | r1_tsep_1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f244,f33])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f243,f35])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f55,f34])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f75,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_3
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2151,plain,(
    ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f2150])).

fof(f2150,plain,
    ( $false
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f2149,f33])).

fof(f2149,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f2148,f35])).

fof(f2148,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f2147,f36])).

fof(f2147,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f2146,f37])).

fof(f2146,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f2145,f38])).

fof(f2145,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f2144,f39])).

fof(f2144,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(resolution,[],[f2106,f60])).

fof(f2106,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f2143,plain,(
    spl4_53 ),
    inference(avatar_contradiction_clause,[],[f2142])).

fof(f2142,plain,
    ( $false
    | spl4_53 ),
    inference(subsumption_resolution,[],[f2141,f33])).

fof(f2141,plain,
    ( v2_struct_0(sK0)
    | spl4_53 ),
    inference(subsumption_resolution,[],[f2140,f35])).

fof(f2140,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_53 ),
    inference(subsumption_resolution,[],[f2139,f36])).

fof(f2139,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_53 ),
    inference(subsumption_resolution,[],[f2138,f37])).

fof(f2138,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_53 ),
    inference(subsumption_resolution,[],[f2137,f38])).

fof(f2137,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_53 ),
    inference(subsumption_resolution,[],[f2136,f39])).

fof(f2136,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_53 ),
    inference(resolution,[],[f2110,f61])).

fof(f2110,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f2108])).

fof(f2121,plain,(
    spl4_51 ),
    inference(avatar_contradiction_clause,[],[f2120])).

fof(f2120,plain,
    ( $false
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2119,f33])).

fof(f2119,plain,
    ( v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2118,f34])).

fof(f2118,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2117,f35])).

fof(f2117,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2116,f36])).

fof(f2116,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2115,f37])).

fof(f2115,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2114,f38])).

fof(f2114,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2113,f39])).

fof(f2113,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(subsumption_resolution,[],[f2112,f42])).

fof(f2112,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_51 ),
    inference(resolution,[],[f2102,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2102,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl4_51 ),
    inference(avatar_component_clause,[],[f2100])).

fof(f2100,plain,
    ( spl4_51
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f2111,plain,
    ( ~ spl4_51
    | spl4_52
    | ~ spl4_53
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f2005,f682,f678,f84,f63,f2108,f2104,f2100])).

fof(f63,plain,
    ( spl4_1
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f84,plain,
    ( spl4_5
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f678,plain,
    ( spl4_34
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f682,plain,
    ( spl4_35
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f2005,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f2004,f36])).

fof(f2004,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1996,f37])).

fof(f1996,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(resolution,[],[f858,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f168,f33])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f35])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f858,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f857,f36])).

fof(f857,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f856,f37])).

fof(f856,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f852,f42])).

fof(f852,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(resolution,[],[f851,f65])).

fof(f65,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f851,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f850,f33])).

fof(f850,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f849,f35])).

fof(f849,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f848,f38])).

fof(f848,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f847,f39])).

fof(f847,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(duplicate_literal_removal,[],[f844])).

fof(f844,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(resolution,[],[f842,f61])).

fof(f842,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f841,f33])).

fof(f841,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f840,f35])).

fof(f840,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f839,f38])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f838,f39])).

fof(f838,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(duplicate_literal_removal,[],[f837])).

fof(f837,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(resolution,[],[f726,f60])).

fof(f726,plain,
    ( ! [X1] :
        ( v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f725,f33])).

fof(f725,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f724,f34])).

fof(f724,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f723,f35])).

fof(f723,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f722,f38])).

fof(f722,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f721,f39])).

fof(f721,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f720,f40])).

fof(f720,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f712,f41])).

fof(f712,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X1,sK2))
        | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(resolution,[],[f710,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_5
    | spl4_34
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f709,f679])).

fof(f679,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f678])).

fof(f709,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2))
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_5
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f564,f683])).

fof(f683,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f682])).

fof(f564,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f563,f36])).

fof(f563,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2))
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f553,f37])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f86,f245])).

fof(f86,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1939,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f1938])).

fof(f1938,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1937,f33])).

fof(f1937,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1936,f34])).

fof(f1936,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1935,f35])).

fof(f1935,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1934,f38])).

fof(f1934,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1933,f39])).

fof(f1933,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1932,f36])).

fof(f1932,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1931,f37])).

fof(f1931,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1930,f534])).

fof(f534,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl4_32
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1930,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(resolution,[],[f1878,f50])).

fof(f1878,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1877,f1778])).

fof(f1778,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f1777,plain,
    ( spl4_49
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f1877,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1876,f1782])).

fof(f1782,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f1781,plain,
    ( spl4_50
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1876,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1875,f36])).

fof(f1875,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1867,f37])).

fof(f1867,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45 ),
    inference(resolution,[],[f1110,f169])).

fof(f1110,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1109,f36])).

fof(f1109,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1108,f37])).

fof(f1108,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_32
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1104,f534])).

fof(f1104,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(resolution,[],[f1103,f65])).

fof(f1103,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1102,f33])).

fof(f1102,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1101,f35])).

fof(f1101,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1100,f38])).

fof(f1100,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1099,f39])).

fof(f1099,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(duplicate_literal_removal,[],[f1096])).

fof(f1096,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(resolution,[],[f1094,f61])).

fof(f1094,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1093,f33])).

fof(f1093,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1092,f35])).

fof(f1092,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1091,f38])).

fof(f1091,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1090,f39])).

fof(f1090,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(duplicate_literal_removal,[],[f1089])).

fof(f1089,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(resolution,[],[f1036,f60])).

fof(f1036,plain,
    ( ! [X0] :
        ( v2_struct_0(k2_tsep_1(sK0,sK2,X0))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1035,f38])).

fof(f1035,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1034,f39])).

fof(f1034,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1033,f40])).

fof(f1033,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1028,f41])).

fof(f1028,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,X0))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(resolution,[],[f1027,f688])).

fof(f1027,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_6
    | spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1026,f1009])).

fof(f1009,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f1008,plain,
    ( spl4_44
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1026,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_6
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f975,f1013])).

fof(f1013,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1012,plain,
    ( spl4_45
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f975,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f974,f36])).

fof(f974,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3))
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f964,f37])).

fof(f964,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f90,f245])).

fof(f90,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_6
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1812,plain,(
    ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f1811])).

fof(f1811,plain,
    ( $false
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1810,f33])).

fof(f1810,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1809,f35])).

fof(f1809,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1808,f38])).

fof(f1808,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1807,f39])).

fof(f1807,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1806,f36])).

fof(f1806,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1805,f37])).

fof(f1805,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_49 ),
    inference(resolution,[],[f1779,f60])).

fof(f1779,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f1804,plain,
    ( ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f1803])).

fof(f1803,plain,
    ( $false
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1802,f33])).

fof(f1802,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1801,f34])).

fof(f1801,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1800,f35])).

fof(f1800,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1799,f38])).

fof(f1799,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1798,f39])).

fof(f1798,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1797,f36])).

fof(f1797,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1796,f37])).

fof(f1796,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_32
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1795,f534])).

fof(f1795,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_31
    | spl4_49
    | ~ spl4_50 ),
    inference(resolution,[],[f1794,f49])).

fof(f1794,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ spl4_31
    | spl4_49
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1793,f1778])).

fof(f1793,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ spl4_31
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1668,f1782])).

fof(f1668,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f1667,f38])).

fof(f1667,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f1658,f39])).

fof(f1658,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ spl4_31 ),
    inference(resolution,[],[f531,f236])).

fof(f531,plain,
    ( r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl4_31
  <=> r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1792,plain,(
    spl4_50 ),
    inference(avatar_contradiction_clause,[],[f1791])).

fof(f1791,plain,
    ( $false
    | spl4_50 ),
    inference(subsumption_resolution,[],[f1790,f33])).

fof(f1790,plain,
    ( v2_struct_0(sK0)
    | spl4_50 ),
    inference(subsumption_resolution,[],[f1789,f35])).

fof(f1789,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_50 ),
    inference(subsumption_resolution,[],[f1788,f38])).

fof(f1788,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_50 ),
    inference(subsumption_resolution,[],[f1787,f39])).

fof(f1787,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_50 ),
    inference(subsumption_resolution,[],[f1786,f36])).

fof(f1786,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_50 ),
    inference(subsumption_resolution,[],[f1785,f37])).

fof(f1785,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_50 ),
    inference(resolution,[],[f1783,f61])).

fof(f1783,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | spl4_50 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f1573,plain,(
    ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f1572])).

fof(f1572,plain,
    ( $false
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1571,f33])).

fof(f1571,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1570,f35])).

fof(f1570,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1569,f40])).

fof(f1569,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1568,f41])).

fof(f1568,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1567,f38])).

fof(f1567,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1566,f39])).

fof(f1566,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_34 ),
    inference(resolution,[],[f680,f60])).

fof(f680,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f678])).

fof(f1316,plain,(
    ~ spl4_44 ),
    inference(avatar_contradiction_clause,[],[f1315])).

fof(f1315,plain,
    ( $false
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1314,f33])).

fof(f1314,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1313,f35])).

fof(f1313,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1312,f38])).

fof(f1312,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1311,f39])).

fof(f1311,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1310,f40])).

fof(f1310,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1309,f41])).

fof(f1309,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_44 ),
    inference(resolution,[],[f1010,f60])).

fof(f1010,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f1266,plain,
    ( ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f1265])).

fof(f1265,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1264,f101])).

fof(f1264,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1263,f154])).

fof(f154,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_13
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1263,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1256,f42])).

fof(f1256,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_32 ),
    inference(resolution,[],[f535,f93])).

fof(f535,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f533])).

fof(f1228,plain,
    ( spl4_2
    | spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1227])).

fof(f1227,plain,
    ( $false
    | spl4_2
    | spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f1195,f89])).

fof(f89,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1195,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f956,f85])).

fof(f85,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f956,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f44,f68])).

fof(f68,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f44,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f1023,plain,(
    spl4_45 ),
    inference(avatar_contradiction_clause,[],[f1022])).

fof(f1022,plain,
    ( $false
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1021,f33])).

fof(f1021,plain,
    ( v2_struct_0(sK0)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1020,f35])).

fof(f1020,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1019,f38])).

fof(f1019,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1018,f39])).

fof(f1018,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1017,f40])).

fof(f1017,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1016,f41])).

fof(f1016,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_45 ),
    inference(resolution,[],[f1014,f61])).

fof(f1014,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f912,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f911])).

fof(f911,plain,
    ( $false
    | spl4_41 ),
    inference(subsumption_resolution,[],[f910,f33])).

fof(f910,plain,
    ( v2_struct_0(sK0)
    | spl4_41 ),
    inference(subsumption_resolution,[],[f909,f36])).

fof(f909,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_41 ),
    inference(subsumption_resolution,[],[f908,f37])).

fof(f908,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_41 ),
    inference(subsumption_resolution,[],[f907,f38])).

fof(f907,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_41 ),
    inference(subsumption_resolution,[],[f906,f39])).

fof(f906,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_41 ),
    inference(subsumption_resolution,[],[f905,f35])).

fof(f905,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_41 ),
    inference(duplicate_literal_removal,[],[f900])).

fof(f900,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_41 ),
    inference(resolution,[],[f899,f61])).

fof(f899,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | spl4_41 ),
    inference(resolution,[],[f893,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f893,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f891])).

fof(f696,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | spl4_35 ),
    inference(subsumption_resolution,[],[f694,f33])).

fof(f694,plain,
    ( v2_struct_0(sK0)
    | spl4_35 ),
    inference(subsumption_resolution,[],[f693,f35])).

fof(f693,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_35 ),
    inference(subsumption_resolution,[],[f692,f40])).

fof(f692,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_35 ),
    inference(subsumption_resolution,[],[f691,f41])).

fof(f691,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_35 ),
    inference(subsumption_resolution,[],[f690,f38])).

fof(f690,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_35 ),
    inference(subsumption_resolution,[],[f689,f39])).

fof(f689,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_35 ),
    inference(resolution,[],[f684,f61])).

fof(f684,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f682])).

fof(f601,plain,(
    ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f599,f33])).

fof(f599,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f598,f35])).

fof(f598,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f597,f40])).

fof(f597,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f596,f41])).

fof(f596,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f595,f36])).

fof(f595,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f594,f37])).

fof(f594,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(resolution,[],[f421,f60])).

fof(f421,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl4_29
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f536,plain,
    ( spl4_31
    | spl4_32
    | ~ spl4_2
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f522,f423,f419,f77,f67,f533,f529])).

fof(f77,plain,
    ( spl4_4
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f423,plain,
    ( spl4_30
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f522,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f521,f39])).

fof(f521,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f516,f38])).

fof(f516,plain,
    ( v2_struct_0(sK2)
    | r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(resolution,[],[f515,f69])).

fof(f515,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f514,f33])).

fof(f514,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f513,f35])).

fof(f513,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f512,f36])).

fof(f512,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f511,f37])).

fof(f511,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(resolution,[],[f506,f61])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f505,f33])).

fof(f505,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f504,f35])).

fof(f504,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f503,f36])).

fof(f503,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f502,f37])).

fof(f502,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(resolution,[],[f475,f60])).

fof(f475,plain,
    ( ! [X0] :
        ( v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f474,f33])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f473,f34])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f472,f35])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f471,f36])).

fof(f471,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f470,f37])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f469,f40])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f468,f41])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,X0,sK1))
        | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(resolution,[],[f53,f445])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK2,X0) )
    | ~ spl4_4
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f444,f420])).

fof(f420,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f419])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK2,X0) )
    | ~ spl4_4
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f443,f424])).

fof(f424,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f423])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK2,X0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f442,f38])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK2,X0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f440,f39])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK2,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f323,f79])).

fof(f79,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | r1_tsep_1(X1,X2) ) ),
    inference(subsumption_resolution,[],[f322,f33])).

fof(f322,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f321,f35])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f434,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl4_30 ),
    inference(subsumption_resolution,[],[f432,f33])).

fof(f432,plain,
    ( v2_struct_0(sK0)
    | spl4_30 ),
    inference(subsumption_resolution,[],[f431,f35])).

fof(f431,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_30 ),
    inference(subsumption_resolution,[],[f430,f40])).

fof(f430,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_30 ),
    inference(subsumption_resolution,[],[f429,f41])).

fof(f429,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_30 ),
    inference(subsumption_resolution,[],[f428,f36])).

fof(f428,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_30 ),
    inference(subsumption_resolution,[],[f427,f37])).

fof(f427,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_30 ),
    inference(resolution,[],[f425,f61])).

fof(f425,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f423])).

fof(f383,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f381,f33])).

fof(f381,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f380,f35])).

fof(f380,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f379,f36])).

fof(f379,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f378,f37])).

fof(f378,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f377,f40])).

fof(f377,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f376,f41])).

fof(f376,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f220,f60])).

fof(f220,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f233,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f231,f33])).

fof(f231,plain,
    ( v2_struct_0(sK0)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f230,f35])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f229,f36])).

fof(f229,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f228,f37])).

fof(f228,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f227,f40])).

fof(f227,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f226,f41])).

fof(f226,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_19 ),
    inference(resolution,[],[f224,f61])).

fof(f224,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f166,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f163,f35])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_13 ),
    inference(resolution,[],[f161,f37])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_13 ),
    inference(resolution,[],[f155,f48])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f113,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_8 ),
    inference(resolution,[],[f108,f39])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_8 ),
    inference(resolution,[],[f102,f48])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f91,plain,
    ( spl4_5
    | spl4_6
    | spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f82,f77,f73,f88,f84])).

fof(f82,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f81,f74])).

fof(f74,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f81,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f46,f78])).

fof(f78,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f46,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,
    ( spl4_3
    | spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f71,f63,f77,f73])).

fof(f71,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f45,f64])).

fof(f64,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f45,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f43,f67,f63])).

fof(f43,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3929)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (3918)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.51  % (3935)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (3920)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.53  % (3930)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (3932)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.53  % (3931)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.54  % (3924)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.54  % (3925)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3927)WARNING: option uwaf not known.
% 0.21/0.54  % (3937)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.54  % (3927)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 1.44/0.54  % (3917)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 1.44/0.55  % (3934)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 1.44/0.55  % (3936)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 1.44/0.55  % (3921)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 1.44/0.56  % (3933)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 1.44/0.56  % (3923)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 1.44/0.56  % (3919)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 1.61/0.56  % (3922)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 1.61/0.58  % (3928)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 1.61/0.58  % (3926)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 2.98/0.74  % (3917)Refutation found. Thanks to Tanya!
% 2.98/0.74  % SZS status Theorem for theBenchmark
% 2.98/0.74  % SZS output start Proof for theBenchmark
% 2.98/0.74  fof(f2311,plain,(
% 2.98/0.74    $false),
% 2.98/0.74    inference(avatar_sat_refutation,[],[f70,f80,f91,f113,f166,f233,f383,f434,f536,f601,f696,f912,f1023,f1228,f1266,f1316,f1573,f1792,f1804,f1812,f1939,f2111,f2121,f2143,f2151,f2310])).
% 2.98/0.74  fof(f2310,plain,(
% 2.98/0.74    ~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f2309])).
% 2.98/0.74  fof(f2309,plain,(
% 2.98/0.74    $false | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2308,f33])).
% 2.98/0.74  fof(f33,plain,(
% 2.98/0.74    ~v2_struct_0(sK0)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f32,plain,(
% 2.98/0.74    ((((((r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)) & m1_pre_topc(sK2,sK3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.98/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f31,f30,f29,f28])).
% 2.98/0.74  fof(f28,plain,(
% 2.98/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.98/0.74    introduced(choice_axiom,[])).
% 2.98/0.74  fof(f29,plain,(
% 2.98/0.74    ? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 2.98/0.74    introduced(choice_axiom,[])).
% 2.98/0.74  fof(f30,plain,(
% 2.98/0.74    ? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2)) & m1_pre_topc(sK2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.98/0.74    introduced(choice_axiom,[])).
% 2.98/0.74  fof(f31,plain,(
% 2.98/0.74    ? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2)) & m1_pre_topc(sK2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((((r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)) & m1_pre_topc(sK2,sK3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 2.98/0.74    introduced(choice_axiom,[])).
% 2.98/0.74  fof(f13,plain,(
% 2.98/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f12])).
% 2.98/0.74  fof(f12,plain,(
% 2.98/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f10])).
% 2.98/0.74  fof(f10,negated_conjecture,(
% 2.98/0.74    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 2.98/0.74    inference(negated_conjecture,[],[f9])).
% 2.98/0.74  fof(f9,conjecture,(
% 2.98/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).
% 2.98/0.74  fof(f2308,plain,(
% 2.98/0.74    v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2307,f34])).
% 2.98/0.74  fof(f34,plain,(
% 2.98/0.74    v2_pre_topc(sK0)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2307,plain,(
% 2.98/0.74    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2306,f35])).
% 2.98/0.74  fof(f35,plain,(
% 2.98/0.74    l1_pre_topc(sK0)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2306,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2305,f36])).
% 2.98/0.74  fof(f36,plain,(
% 2.98/0.74    ~v2_struct_0(sK1)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2305,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2304,f37])).
% 2.98/0.74  fof(f37,plain,(
% 2.98/0.74    m1_pre_topc(sK1,sK0)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2304,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2303,f38])).
% 2.98/0.74  fof(f38,plain,(
% 2.98/0.74    ~v2_struct_0(sK2)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2303,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2302,f39])).
% 2.98/0.74  fof(f39,plain,(
% 2.98/0.74    m1_pre_topc(sK2,sK0)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2302,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2301,f42])).
% 2.98/0.74  fof(f42,plain,(
% 2.98/0.74    ~r1_tsep_1(sK1,sK2)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f2301,plain,(
% 2.98/0.74    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(resolution,[],[f2249,f50])).
% 2.98/0.74  fof(f50,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f17])).
% 2.98/0.74  fof(f17,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f16])).
% 2.98/0.74  fof(f16,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f7])).
% 2.98/0.74  fof(f7,axiom,(
% 2.98/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).
% 2.98/0.74  fof(f2249,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | spl4_52 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2248,f2105])).
% 2.98/0.74  fof(f2105,plain,(
% 2.98/0.74    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl4_52),
% 2.98/0.74    inference(avatar_component_clause,[],[f2104])).
% 2.98/0.74  fof(f2104,plain,(
% 2.98/0.74    spl4_52 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.98/0.74  fof(f2248,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41 | ~spl4_53)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2247,f2109])).
% 2.98/0.74  fof(f2109,plain,(
% 2.98/0.74    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~spl4_53),
% 2.98/0.74    inference(avatar_component_clause,[],[f2108])).
% 2.98/0.74  fof(f2108,plain,(
% 2.98/0.74    spl4_53 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.98/0.74  fof(f2247,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2246,f38])).
% 2.98/0.74  fof(f2246,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2237,f39])).
% 2.98/0.74  fof(f2237,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41)),
% 2.98/0.74    inference(resolution,[],[f2216,f236])).
% 2.98/0.74  fof(f236,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f235,f33])).
% 2.98/0.74  fof(f235,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X1,X0) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f234,f35])).
% 2.98/0.74  fof(f234,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~r1_tsep_1(X1,X0) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(resolution,[],[f52,f34])).
% 2.98/0.74  fof(f52,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(X2,X1) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f19])).
% 2.98/0.74  fof(f19,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f18])).
% 2.98/0.74  fof(f18,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f5])).
% 2.98/0.74  fof(f5,axiom,(
% 2.98/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 2.98/0.74  fof(f2216,plain,(
% 2.98/0.74    r1_tsep_1(sK2,k2_tsep_1(sK0,sK1,sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19 | ~spl4_41)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2215,f892])).
% 2.98/0.74  fof(f892,plain,(
% 2.98/0.74    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_41),
% 2.98/0.74    inference(avatar_component_clause,[],[f891])).
% 2.98/0.74  fof(f891,plain,(
% 2.98/0.74    spl4_41 <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.98/0.74  fof(f2215,plain,(
% 2.98/0.74    r1_tsep_1(sK2,k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2208,f101])).
% 2.98/0.74  fof(f101,plain,(
% 2.98/0.74    l1_pre_topc(sK2) | ~spl4_8),
% 2.98/0.74    inference(avatar_component_clause,[],[f100])).
% 2.98/0.74  fof(f100,plain,(
% 2.98/0.74    spl4_8 <=> l1_pre_topc(sK2)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.98/0.74  fof(f2208,plain,(
% 2.98/0.74    r1_tsep_1(sK2,k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | (~spl4_2 | ~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(resolution,[],[f1555,f93])).
% 2.98/0.74  fof(f93,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~r1_tsep_1(X1,X0) | r1_tsep_1(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 2.98/0.74    inference(resolution,[],[f92,f47])).
% 2.98/0.74  fof(f47,plain,(
% 2.98/0.74    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f14])).
% 2.98/0.74  fof(f14,plain,(
% 2.98/0.74    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.98/0.74    inference(ennf_transformation,[],[f1])).
% 2.98/0.74  fof(f1,axiom,(
% 2.98/0.74    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.98/0.74  fof(f92,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 2.98/0.74    inference(resolution,[],[f59,f47])).
% 2.98/0.74  fof(f59,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f25])).
% 2.98/0.74  fof(f25,plain,(
% 2.98/0.74    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f24])).
% 2.98/0.74  fof(f24,plain,(
% 2.98/0.74    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f4])).
% 2.98/0.74  fof(f4,axiom,(
% 2.98/0.74    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 2.98/0.74  fof(f1555,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1554,f38])).
% 2.98/0.74  fof(f1554,plain,(
% 2.98/0.74    v2_struct_0(sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1553,f39])).
% 2.98/0.74  fof(f1553,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1544,f42])).
% 2.98/0.74  fof(f1544,plain,(
% 2.98/0.74    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | ~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(resolution,[],[f1542,f69])).
% 2.98/0.74  fof(f69,plain,(
% 2.98/0.74    m1_pre_topc(sK2,sK3) | ~spl4_2),
% 2.98/0.74    inference(avatar_component_clause,[],[f67])).
% 2.98/0.74  fof(f67,plain,(
% 2.98/0.74    spl4_2 <=> m1_pre_topc(sK2,sK3)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.98/0.74  fof(f1542,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1541,f33])).
% 2.98/0.74  fof(f1541,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1540,f35])).
% 2.98/0.74  fof(f1540,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1539,f36])).
% 2.98/0.74  fof(f1539,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1538,f37])).
% 2.98/0.74  fof(f1538,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f1535])).
% 2.98/0.74  fof(f1535,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(resolution,[],[f1453,f61])).
% 2.98/0.74  fof(f61,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f27])).
% 2.98/0.74  fof(f27,plain,(
% 2.98/0.74    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f26])).
% 2.98/0.74  fof(f26,plain,(
% 2.98/0.74    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f11])).
% 2.98/0.74  fof(f11,plain,(
% 2.98/0.74    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 2.98/0.74    inference(pure_predicate_removal,[],[f3])).
% 2.98/0.74  fof(f3,axiom,(
% 2.98/0.74    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 2.98/0.74  fof(f1453,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1452,f33])).
% 2.98/0.74  fof(f1452,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1451,f35])).
% 2.98/0.74  fof(f1451,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1450,f36])).
% 2.98/0.74  fof(f1450,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1449,f37])).
% 2.98/0.74  fof(f1449,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f1448])).
% 2.98/0.74  fof(f1448,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(resolution,[],[f1401,f60])).
% 2.98/0.74  fof(f60,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f27])).
% 2.98/0.74  fof(f1401,plain,(
% 2.98/0.74    ( ! [X0] : (v2_struct_0(k2_tsep_1(sK0,sK1,X0)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1400,f36])).
% 2.98/0.74  fof(f1400,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1399,f37])).
% 2.98/0.74  fof(f1399,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1398,f40])).
% 2.98/0.74  fof(f40,plain,(
% 2.98/0.74    ~v2_struct_0(sK3)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f1398,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1393,f41])).
% 2.98/0.74  fof(f41,plain,(
% 2.98/0.74    m1_pre_topc(sK3,sK0)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f1393,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK1,X0),sK2) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(resolution,[],[f1214,f688])).
% 2.98/0.74  fof(f688,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(sK0,X2,X0),k2_tsep_1(sK0,X2,X1)) | r1_tsep_1(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X0,X1)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f687,f33])).
% 2.98/0.74  fof(f687,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | r1_tsep_1(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | m1_pre_topc(k2_tsep_1(sK0,X2,X0),k2_tsep_1(sK0,X2,X1)) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f686,f35])).
% 2.98/0.74  fof(f686,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | r1_tsep_1(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | m1_pre_topc(k2_tsep_1(sK0,X2,X0),k2_tsep_1(sK0,X2,X1)) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(resolution,[],[f54,f34])).
% 2.98/0.74  fof(f54,plain,(
% 2.98/0.74    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f21])).
% 2.98/0.74  fof(f21,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f20])).
% 2.98/0.74  fof(f20,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f8])).
% 2.98/0.74  fof(f8,axiom,(
% 2.98/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).
% 2.98/0.74  fof(f1214,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK2)) ) | (~spl4_3 | spl4_18 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1213,f219])).
% 2.98/0.74  fof(f219,plain,(
% 2.98/0.74    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | spl4_18),
% 2.98/0.74    inference(avatar_component_clause,[],[f218])).
% 2.98/0.74  fof(f218,plain,(
% 2.98/0.74    spl4_18 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.98/0.74  fof(f1213,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK2)) ) | (~spl4_3 | ~spl4_19)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1212,f223])).
% 2.98/0.74  fof(f223,plain,(
% 2.98/0.74    m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | ~spl4_19),
% 2.98/0.74    inference(avatar_component_clause,[],[f222])).
% 2.98/0.74  fof(f222,plain,(
% 2.98/0.74    spl4_19 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.98/0.74  fof(f1212,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK2)) ) | ~spl4_3),
% 2.98/0.74    inference(subsumption_resolution,[],[f1211,f38])).
% 2.98/0.74  fof(f1211,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3)) | v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK2)) ) | ~spl4_3),
% 2.98/0.74    inference(subsumption_resolution,[],[f1201,f39])).
% 2.98/0.74  fof(f1201,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK2)) ) | ~spl4_3),
% 2.98/0.74    inference(resolution,[],[f75,f245])).
% 2.98/0.74  fof(f245,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | r1_tsep_1(X2,X1)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f244,f33])).
% 2.98/0.74  fof(f244,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | r1_tsep_1(X2,X1) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f243,f35])).
% 2.98/0.74  fof(f243,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | r1_tsep_1(X2,X1) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(resolution,[],[f55,f34])).
% 2.98/0.74  fof(f55,plain,(
% 2.98/0.74    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X1,X3) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f23])).
% 2.98/0.74  fof(f23,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.98/0.74    inference(flattening,[],[f22])).
% 2.98/0.74  fof(f22,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.98/0.74    inference(ennf_transformation,[],[f6])).
% 2.98/0.74  fof(f6,axiom,(
% 2.98/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 2.98/0.74  fof(f75,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | ~spl4_3),
% 2.98/0.74    inference(avatar_component_clause,[],[f73])).
% 2.98/0.74  fof(f73,plain,(
% 2.98/0.74    spl4_3 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.98/0.74  fof(f2151,plain,(
% 2.98/0.74    ~spl4_52),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f2150])).
% 2.98/0.74  fof(f2150,plain,(
% 2.98/0.74    $false | ~spl4_52),
% 2.98/0.74    inference(subsumption_resolution,[],[f2149,f33])).
% 2.98/0.74  fof(f2149,plain,(
% 2.98/0.74    v2_struct_0(sK0) | ~spl4_52),
% 2.98/0.74    inference(subsumption_resolution,[],[f2148,f35])).
% 2.98/0.74  fof(f2148,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_52),
% 2.98/0.74    inference(subsumption_resolution,[],[f2147,f36])).
% 2.98/0.74  fof(f2147,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_52),
% 2.98/0.74    inference(subsumption_resolution,[],[f2146,f37])).
% 2.98/0.74  fof(f2146,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_52),
% 2.98/0.74    inference(subsumption_resolution,[],[f2145,f38])).
% 2.98/0.74  fof(f2145,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_52),
% 2.98/0.74    inference(subsumption_resolution,[],[f2144,f39])).
% 2.98/0.74  fof(f2144,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_52),
% 2.98/0.74    inference(resolution,[],[f2106,f60])).
% 2.98/0.74  fof(f2106,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_52),
% 2.98/0.74    inference(avatar_component_clause,[],[f2104])).
% 2.98/0.74  fof(f2143,plain,(
% 2.98/0.74    spl4_53),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f2142])).
% 2.98/0.74  fof(f2142,plain,(
% 2.98/0.74    $false | spl4_53),
% 2.98/0.74    inference(subsumption_resolution,[],[f2141,f33])).
% 2.98/0.74  fof(f2141,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_53),
% 2.98/0.74    inference(subsumption_resolution,[],[f2140,f35])).
% 2.98/0.74  fof(f2140,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_53),
% 2.98/0.74    inference(subsumption_resolution,[],[f2139,f36])).
% 2.98/0.74  fof(f2139,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_53),
% 2.98/0.74    inference(subsumption_resolution,[],[f2138,f37])).
% 2.98/0.74  fof(f2138,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_53),
% 2.98/0.74    inference(subsumption_resolution,[],[f2137,f38])).
% 2.98/0.74  fof(f2137,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_53),
% 2.98/0.74    inference(subsumption_resolution,[],[f2136,f39])).
% 2.98/0.74  fof(f2136,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_53),
% 2.98/0.74    inference(resolution,[],[f2110,f61])).
% 2.98/0.74  fof(f2110,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_53),
% 2.98/0.74    inference(avatar_component_clause,[],[f2108])).
% 2.98/0.74  fof(f2121,plain,(
% 2.98/0.74    spl4_51),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f2120])).
% 2.98/0.74  fof(f2120,plain,(
% 2.98/0.74    $false | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2119,f33])).
% 2.98/0.74  fof(f2119,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2118,f34])).
% 2.98/0.74  fof(f2118,plain,(
% 2.98/0.74    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2117,f35])).
% 2.98/0.74  fof(f2117,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2116,f36])).
% 2.98/0.74  fof(f2116,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2115,f37])).
% 2.98/0.74  fof(f2115,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2114,f38])).
% 2.98/0.74  fof(f2114,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2113,f39])).
% 2.98/0.74  fof(f2113,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(subsumption_resolution,[],[f2112,f42])).
% 2.98/0.74  fof(f2112,plain,(
% 2.98/0.74    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_51),
% 2.98/0.74    inference(resolution,[],[f2102,f49])).
% 2.98/0.74  fof(f49,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f17])).
% 2.98/0.74  fof(f2102,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | spl4_51),
% 2.98/0.74    inference(avatar_component_clause,[],[f2100])).
% 2.98/0.74  fof(f2100,plain,(
% 2.98/0.74    spl4_51 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.98/0.74  fof(f2111,plain,(
% 2.98/0.74    ~spl4_51 | spl4_52 | ~spl4_53 | ~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35),
% 2.98/0.74    inference(avatar_split_clause,[],[f2005,f682,f678,f84,f63,f2108,f2104,f2100])).
% 2.98/0.74  fof(f63,plain,(
% 2.98/0.74    spl4_1 <=> m1_pre_topc(sK1,sK3)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.98/0.74  fof(f84,plain,(
% 2.98/0.74    spl4_5 <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.98/0.74  fof(f678,plain,(
% 2.98/0.74    spl4_34 <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK2))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.98/0.74  fof(f682,plain,(
% 2.98/0.74    spl4_35 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 2.98/0.74  fof(f2005,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f2004,f36])).
% 2.98/0.74  fof(f2004,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1996,f37])).
% 2.98/0.74  fof(f1996,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(resolution,[],[f858,f169])).
% 2.98/0.74  fof(f169,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f168,f33])).
% 2.98/0.74  fof(f168,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X0,X1) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f167,f35])).
% 2.98/0.74  fof(f167,plain,(
% 2.98/0.74    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~r1_tsep_1(X0,X1) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(resolution,[],[f51,f34])).
% 2.98/0.74  fof(f51,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f19])).
% 2.98/0.74  fof(f858,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f857,f36])).
% 2.98/0.74  fof(f857,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f856,f37])).
% 2.98/0.74  fof(f856,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f852,f42])).
% 2.98/0.74  fof(f852,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(resolution,[],[f851,f65])).
% 2.98/0.74  fof(f65,plain,(
% 2.98/0.74    m1_pre_topc(sK1,sK3) | ~spl4_1),
% 2.98/0.74    inference(avatar_component_clause,[],[f63])).
% 2.98/0.74  fof(f851,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f850,f33])).
% 2.98/0.74  fof(f850,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f849,f35])).
% 2.98/0.74  fof(f849,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f848,f38])).
% 2.98/0.74  fof(f848,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f847,f39])).
% 2.98/0.74  fof(f847,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f844])).
% 2.98/0.74  fof(f844,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(resolution,[],[f842,f61])).
% 2.98/0.74  fof(f842,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f841,f33])).
% 2.98/0.74  fof(f841,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f840,f35])).
% 2.98/0.74  fof(f840,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f839,f38])).
% 2.98/0.74  fof(f839,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f838,f39])).
% 2.98/0.74  fof(f838,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f837])).
% 2.98/0.74  fof(f837,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X0,sK2),sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(resolution,[],[f726,f60])).
% 2.98/0.74  fof(f726,plain,(
% 2.98/0.74    ( ! [X1] : (v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f725,f33])).
% 2.98/0.74  fof(f725,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f724,f34])).
% 2.98/0.74  fof(f724,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f723,f35])).
% 2.98/0.74  fof(f723,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f722,f38])).
% 2.98/0.74  fof(f722,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f721,f39])).
% 2.98/0.74  fof(f721,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f720,f40])).
% 2.98/0.74  fof(f720,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f712,f41])).
% 2.98/0.74  fof(f712,plain,(
% 2.98/0.74    ( ! [X1] : (~m1_pre_topc(k2_tsep_1(sK0,X1,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(resolution,[],[f710,f53])).
% 2.98/0.74  fof(f53,plain,(
% 2.98/0.74    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f21])).
% 2.98/0.74  fof(f710,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | (~spl4_5 | spl4_34 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f709,f679])).
% 2.98/0.74  fof(f679,plain,(
% 2.98/0.74    ~v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | spl4_34),
% 2.98/0.74    inference(avatar_component_clause,[],[f678])).
% 2.98/0.74  fof(f709,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | (~spl4_5 | ~spl4_35)),
% 2.98/0.74    inference(subsumption_resolution,[],[f564,f683])).
% 2.98/0.74  fof(f683,plain,(
% 2.98/0.74    m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) | ~spl4_35),
% 2.98/0.74    inference(avatar_component_clause,[],[f682])).
% 2.98/0.74  fof(f564,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | ~spl4_5),
% 2.98/0.74    inference(subsumption_resolution,[],[f563,f36])).
% 2.98/0.74  fof(f563,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | ~spl4_5),
% 2.98/0.74    inference(subsumption_resolution,[],[f553,f37])).
% 2.98/0.74  fof(f553,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | ~spl4_5),
% 2.98/0.74    inference(resolution,[],[f86,f245])).
% 2.98/0.74  fof(f86,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | ~spl4_5),
% 2.98/0.74    inference(avatar_component_clause,[],[f84])).
% 2.98/0.74  fof(f1939,plain,(
% 2.98/0.74    ~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1938])).
% 2.98/0.74  fof(f1938,plain,(
% 2.98/0.74    $false | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1937,f33])).
% 2.98/0.74  fof(f1937,plain,(
% 2.98/0.74    v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1936,f34])).
% 2.98/0.74  fof(f1936,plain,(
% 2.98/0.74    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1935,f35])).
% 2.98/0.74  fof(f1935,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1934,f38])).
% 2.98/0.74  fof(f1934,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1933,f39])).
% 2.98/0.74  fof(f1933,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1932,f36])).
% 2.98/0.74  fof(f1932,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1931,f37])).
% 2.98/0.74  fof(f1931,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1930,f534])).
% 2.98/0.74  fof(f534,plain,(
% 2.98/0.74    ~r1_tsep_1(sK2,sK1) | spl4_32),
% 2.98/0.74    inference(avatar_component_clause,[],[f533])).
% 2.98/0.74  fof(f533,plain,(
% 2.98/0.74    spl4_32 <=> r1_tsep_1(sK2,sK1)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.98/0.74  fof(f1930,plain,(
% 2.98/0.74    r1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(resolution,[],[f1878,f50])).
% 2.98/0.74  fof(f1878,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1877,f1778])).
% 2.98/0.74  fof(f1778,plain,(
% 2.98/0.74    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | spl4_49),
% 2.98/0.74    inference(avatar_component_clause,[],[f1777])).
% 2.98/0.74  fof(f1777,plain,(
% 2.98/0.74    spl4_49 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK1))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.98/0.74  fof(f1877,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1876,f1782])).
% 2.98/0.74  fof(f1782,plain,(
% 2.98/0.74    m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | ~spl4_50),
% 2.98/0.74    inference(avatar_component_clause,[],[f1781])).
% 2.98/0.74  fof(f1781,plain,(
% 2.98/0.74    spl4_50 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 2.98/0.74  fof(f1876,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1875,f36])).
% 2.98/0.74  fof(f1875,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1867,f37])).
% 2.98/0.74  fof(f1867,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(resolution,[],[f1110,f169])).
% 2.98/0.74  fof(f1110,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1109,f36])).
% 2.98/0.74  fof(f1109,plain,(
% 2.98/0.74    v2_struct_0(sK1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1108,f37])).
% 2.98/0.74  fof(f1108,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_32 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1104,f534])).
% 2.98/0.74  fof(f1104,plain,(
% 2.98/0.74    r1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1) | (~spl4_1 | ~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(resolution,[],[f1103,f65])).
% 2.98/0.74  fof(f1103,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1102,f33])).
% 2.98/0.74  fof(f1102,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1101,f35])).
% 2.98/0.74  fof(f1101,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1100,f38])).
% 2.98/0.74  fof(f1100,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1099,f39])).
% 2.98/0.74  fof(f1099,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f1096])).
% 2.98/0.74  fof(f1096,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(resolution,[],[f1094,f61])).
% 2.98/0.74  fof(f1094,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1093,f33])).
% 2.98/0.74  fof(f1093,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1092,f35])).
% 2.98/0.74  fof(f1092,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1091,f38])).
% 2.98/0.74  fof(f1091,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1090,f39])).
% 2.98/0.74  fof(f1090,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f1089])).
% 2.98/0.74  fof(f1089,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(resolution,[],[f1036,f60])).
% 2.98/0.74  fof(f1036,plain,(
% 2.98/0.74    ( ! [X0] : (v2_struct_0(k2_tsep_1(sK0,sK2,X0)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1035,f38])).
% 2.98/0.74  fof(f1035,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1034,f39])).
% 2.98/0.74  fof(f1034,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1033,f40])).
% 2.98/0.74  fof(f1033,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1028,f41])).
% 2.98/0.74  fof(f1028,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,X0),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,X0)) | r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(resolution,[],[f1027,f688])).
% 2.98/0.74  fof(f1027,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | (~spl4_6 | spl4_44 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1026,f1009])).
% 2.98/0.74  fof(f1009,plain,(
% 2.98/0.74    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | spl4_44),
% 2.98/0.74    inference(avatar_component_clause,[],[f1008])).
% 2.98/0.74  fof(f1008,plain,(
% 2.98/0.74    spl4_44 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.98/0.74  fof(f1026,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3)) | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | (~spl4_6 | ~spl4_45)),
% 2.98/0.74    inference(subsumption_resolution,[],[f975,f1013])).
% 2.98/0.74  fof(f1013,plain,(
% 2.98/0.74    m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | ~spl4_45),
% 2.98/0.74    inference(avatar_component_clause,[],[f1012])).
% 2.98/0.74  fof(f1012,plain,(
% 2.98/0.74    spl4_45 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.98/0.74  fof(f975,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | ~spl4_6),
% 2.98/0.74    inference(subsumption_resolution,[],[f974,f36])).
% 2.98/0.74  fof(f974,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3)) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | ~spl4_6),
% 2.98/0.74    inference(subsumption_resolution,[],[f964,f37])).
% 2.98/0.74  fof(f964,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1)) ) | ~spl4_6),
% 2.98/0.74    inference(resolution,[],[f90,f245])).
% 2.98/0.74  fof(f90,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | ~spl4_6),
% 2.98/0.74    inference(avatar_component_clause,[],[f88])).
% 2.98/0.74  fof(f88,plain,(
% 2.98/0.74    spl4_6 <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.98/0.74  fof(f1812,plain,(
% 2.98/0.74    ~spl4_49),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1811])).
% 2.98/0.74  fof(f1811,plain,(
% 2.98/0.74    $false | ~spl4_49),
% 2.98/0.74    inference(subsumption_resolution,[],[f1810,f33])).
% 2.98/0.74  fof(f1810,plain,(
% 2.98/0.74    v2_struct_0(sK0) | ~spl4_49),
% 2.98/0.74    inference(subsumption_resolution,[],[f1809,f35])).
% 2.98/0.74  fof(f1809,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_49),
% 2.98/0.74    inference(subsumption_resolution,[],[f1808,f38])).
% 2.98/0.74  fof(f1808,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_49),
% 2.98/0.74    inference(subsumption_resolution,[],[f1807,f39])).
% 2.98/0.74  fof(f1807,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_49),
% 2.98/0.74    inference(subsumption_resolution,[],[f1806,f36])).
% 2.98/0.74  fof(f1806,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_49),
% 2.98/0.74    inference(subsumption_resolution,[],[f1805,f37])).
% 2.98/0.74  fof(f1805,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_49),
% 2.98/0.74    inference(resolution,[],[f1779,f60])).
% 2.98/0.74  fof(f1779,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~spl4_49),
% 2.98/0.74    inference(avatar_component_clause,[],[f1777])).
% 2.98/0.74  fof(f1804,plain,(
% 2.98/0.74    ~spl4_31 | spl4_32 | spl4_49 | ~spl4_50),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1803])).
% 2.98/0.74  fof(f1803,plain,(
% 2.98/0.74    $false | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1802,f33])).
% 2.98/0.74  fof(f1802,plain,(
% 2.98/0.74    v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1801,f34])).
% 2.98/0.74  fof(f1801,plain,(
% 2.98/0.74    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1800,f35])).
% 2.98/0.74  fof(f1800,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1799,f38])).
% 2.98/0.74  fof(f1799,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1798,f39])).
% 2.98/0.74  fof(f1798,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1797,f36])).
% 2.98/0.74  fof(f1797,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1796,f37])).
% 2.98/0.74  fof(f1796,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_32 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1795,f534])).
% 2.98/0.74  fof(f1795,plain,(
% 2.98/0.74    r1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_31 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(resolution,[],[f1794,f49])).
% 2.98/0.74  fof(f1794,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2) | (~spl4_31 | spl4_49 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1793,f1778])).
% 2.98/0.74  fof(f1793,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2) | (~spl4_31 | ~spl4_50)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1668,f1782])).
% 2.98/0.74  fof(f1668,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2) | ~spl4_31),
% 2.98/0.74    inference(subsumption_resolution,[],[f1667,f38])).
% 2.98/0.74  fof(f1667,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2) | ~spl4_31),
% 2.98/0.74    inference(subsumption_resolution,[],[f1658,f39])).
% 2.98/0.74  fof(f1658,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2) | ~spl4_31),
% 2.98/0.74    inference(resolution,[],[f531,f236])).
% 2.98/0.74  fof(f531,plain,(
% 2.98/0.74    r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1)) | ~spl4_31),
% 2.98/0.74    inference(avatar_component_clause,[],[f529])).
% 2.98/0.74  fof(f529,plain,(
% 2.98/0.74    spl4_31 <=> r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.98/0.74  fof(f1792,plain,(
% 2.98/0.74    spl4_50),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1791])).
% 2.98/0.74  fof(f1791,plain,(
% 2.98/0.74    $false | spl4_50),
% 2.98/0.74    inference(subsumption_resolution,[],[f1790,f33])).
% 2.98/0.74  fof(f1790,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_50),
% 2.98/0.74    inference(subsumption_resolution,[],[f1789,f35])).
% 2.98/0.74  fof(f1789,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_50),
% 2.98/0.74    inference(subsumption_resolution,[],[f1788,f38])).
% 2.98/0.74  fof(f1788,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_50),
% 2.98/0.74    inference(subsumption_resolution,[],[f1787,f39])).
% 2.98/0.74  fof(f1787,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_50),
% 2.98/0.74    inference(subsumption_resolution,[],[f1786,f36])).
% 2.98/0.74  fof(f1786,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_50),
% 2.98/0.74    inference(subsumption_resolution,[],[f1785,f37])).
% 2.98/0.74  fof(f1785,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_50),
% 2.98/0.74    inference(resolution,[],[f1783,f61])).
% 2.98/0.74  fof(f1783,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | spl4_50),
% 2.98/0.74    inference(avatar_component_clause,[],[f1781])).
% 2.98/0.74  fof(f1573,plain,(
% 2.98/0.74    ~spl4_34),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1572])).
% 2.98/0.74  fof(f1572,plain,(
% 2.98/0.74    $false | ~spl4_34),
% 2.98/0.74    inference(subsumption_resolution,[],[f1571,f33])).
% 2.98/0.74  fof(f1571,plain,(
% 2.98/0.74    v2_struct_0(sK0) | ~spl4_34),
% 2.98/0.74    inference(subsumption_resolution,[],[f1570,f35])).
% 2.98/0.74  fof(f1570,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_34),
% 2.98/0.74    inference(subsumption_resolution,[],[f1569,f40])).
% 2.98/0.74  fof(f1569,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_34),
% 2.98/0.74    inference(subsumption_resolution,[],[f1568,f41])).
% 2.98/0.74  fof(f1568,plain,(
% 2.98/0.74    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_34),
% 2.98/0.74    inference(subsumption_resolution,[],[f1567,f38])).
% 2.98/0.74  fof(f1567,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_34),
% 2.98/0.74    inference(subsumption_resolution,[],[f1566,f39])).
% 2.98/0.74  fof(f1566,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_34),
% 2.98/0.74    inference(resolution,[],[f680,f60])).
% 2.98/0.74  fof(f680,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | ~spl4_34),
% 2.98/0.74    inference(avatar_component_clause,[],[f678])).
% 2.98/0.74  fof(f1316,plain,(
% 2.98/0.74    ~spl4_44),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1315])).
% 2.98/0.74  fof(f1315,plain,(
% 2.98/0.74    $false | ~spl4_44),
% 2.98/0.74    inference(subsumption_resolution,[],[f1314,f33])).
% 2.98/0.74  fof(f1314,plain,(
% 2.98/0.74    v2_struct_0(sK0) | ~spl4_44),
% 2.98/0.74    inference(subsumption_resolution,[],[f1313,f35])).
% 2.98/0.74  fof(f1313,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_44),
% 2.98/0.74    inference(subsumption_resolution,[],[f1312,f38])).
% 2.98/0.74  fof(f1312,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_44),
% 2.98/0.74    inference(subsumption_resolution,[],[f1311,f39])).
% 2.98/0.74  fof(f1311,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_44),
% 2.98/0.74    inference(subsumption_resolution,[],[f1310,f40])).
% 2.98/0.74  fof(f1310,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_44),
% 2.98/0.74    inference(subsumption_resolution,[],[f1309,f41])).
% 2.98/0.74  fof(f1309,plain,(
% 2.98/0.74    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_44),
% 2.98/0.74    inference(resolution,[],[f1010,f60])).
% 2.98/0.74  fof(f1010,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | ~spl4_44),
% 2.98/0.74    inference(avatar_component_clause,[],[f1008])).
% 2.98/0.74  fof(f1266,plain,(
% 2.98/0.74    ~spl4_8 | ~spl4_13 | ~spl4_32),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1265])).
% 2.98/0.74  fof(f1265,plain,(
% 2.98/0.74    $false | (~spl4_8 | ~spl4_13 | ~spl4_32)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1264,f101])).
% 2.98/0.74  fof(f1264,plain,(
% 2.98/0.74    ~l1_pre_topc(sK2) | (~spl4_13 | ~spl4_32)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1263,f154])).
% 2.98/0.74  fof(f154,plain,(
% 2.98/0.74    l1_pre_topc(sK1) | ~spl4_13),
% 2.98/0.74    inference(avatar_component_clause,[],[f153])).
% 2.98/0.74  fof(f153,plain,(
% 2.98/0.74    spl4_13 <=> l1_pre_topc(sK1)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.98/0.74  fof(f1263,plain,(
% 2.98/0.74    ~l1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~spl4_32),
% 2.98/0.74    inference(subsumption_resolution,[],[f1256,f42])).
% 2.98/0.74  fof(f1256,plain,(
% 2.98/0.74    r1_tsep_1(sK1,sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~spl4_32),
% 2.98/0.74    inference(resolution,[],[f535,f93])).
% 2.98/0.74  fof(f535,plain,(
% 2.98/0.74    r1_tsep_1(sK2,sK1) | ~spl4_32),
% 2.98/0.74    inference(avatar_component_clause,[],[f533])).
% 2.98/0.74  fof(f1228,plain,(
% 2.98/0.74    spl4_2 | spl4_5 | spl4_6),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1227])).
% 2.98/0.74  fof(f1227,plain,(
% 2.98/0.74    $false | (spl4_2 | spl4_5 | spl4_6)),
% 2.98/0.74    inference(subsumption_resolution,[],[f1195,f89])).
% 2.98/0.74  fof(f89,plain,(
% 2.98/0.74    ~r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | spl4_6),
% 2.98/0.74    inference(avatar_component_clause,[],[f88])).
% 2.98/0.74  fof(f1195,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | (spl4_2 | spl4_5)),
% 2.98/0.74    inference(subsumption_resolution,[],[f956,f85])).
% 2.98/0.74  fof(f85,plain,(
% 2.98/0.74    ~r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | spl4_5),
% 2.98/0.74    inference(avatar_component_clause,[],[f84])).
% 2.98/0.74  fof(f956,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | spl4_2),
% 2.98/0.74    inference(subsumption_resolution,[],[f44,f68])).
% 2.98/0.74  fof(f68,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK3) | spl4_2),
% 2.98/0.74    inference(avatar_component_clause,[],[f67])).
% 2.98/0.74  fof(f44,plain,(
% 2.98/0.74    m1_pre_topc(sK2,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.98/0.74    inference(cnf_transformation,[],[f32])).
% 2.98/0.74  fof(f1023,plain,(
% 2.98/0.74    spl4_45),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f1022])).
% 2.98/0.74  fof(f1022,plain,(
% 2.98/0.74    $false | spl4_45),
% 2.98/0.74    inference(subsumption_resolution,[],[f1021,f33])).
% 2.98/0.74  fof(f1021,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_45),
% 2.98/0.74    inference(subsumption_resolution,[],[f1020,f35])).
% 2.98/0.74  fof(f1020,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_45),
% 2.98/0.74    inference(subsumption_resolution,[],[f1019,f38])).
% 2.98/0.74  fof(f1019,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_45),
% 2.98/0.74    inference(subsumption_resolution,[],[f1018,f39])).
% 2.98/0.74  fof(f1018,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_45),
% 2.98/0.74    inference(subsumption_resolution,[],[f1017,f40])).
% 2.98/0.74  fof(f1017,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_45),
% 2.98/0.74    inference(subsumption_resolution,[],[f1016,f41])).
% 2.98/0.74  fof(f1016,plain,(
% 2.98/0.74    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_45),
% 2.98/0.74    inference(resolution,[],[f1014,f61])).
% 2.98/0.74  fof(f1014,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | spl4_45),
% 2.98/0.74    inference(avatar_component_clause,[],[f1012])).
% 2.98/0.74  fof(f912,plain,(
% 2.98/0.74    spl4_41),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f911])).
% 2.98/0.74  fof(f911,plain,(
% 2.98/0.74    $false | spl4_41),
% 2.98/0.74    inference(subsumption_resolution,[],[f910,f33])).
% 2.98/0.74  fof(f910,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(subsumption_resolution,[],[f909,f36])).
% 2.98/0.74  fof(f909,plain,(
% 2.98/0.74    v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(subsumption_resolution,[],[f908,f37])).
% 2.98/0.74  fof(f908,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(subsumption_resolution,[],[f907,f38])).
% 2.98/0.74  fof(f907,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(subsumption_resolution,[],[f906,f39])).
% 2.98/0.74  fof(f906,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(subsumption_resolution,[],[f905,f35])).
% 2.98/0.74  fof(f905,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f900])).
% 2.98/0.74  fof(f900,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_41),
% 2.98/0.74    inference(resolution,[],[f899,f61])).
% 2.98/0.74  fof(f899,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | spl4_41),
% 2.98/0.74    inference(resolution,[],[f893,f48])).
% 2.98/0.74  fof(f48,plain,(
% 2.98/0.74    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f15])).
% 2.98/0.74  fof(f15,plain,(
% 2.98/0.74    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.98/0.74    inference(ennf_transformation,[],[f2])).
% 2.98/0.74  fof(f2,axiom,(
% 2.98/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.98/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.98/0.74  fof(f893,plain,(
% 2.98/0.74    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | spl4_41),
% 2.98/0.74    inference(avatar_component_clause,[],[f891])).
% 2.98/0.74  fof(f696,plain,(
% 2.98/0.74    spl4_35),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f695])).
% 2.98/0.74  fof(f695,plain,(
% 2.98/0.74    $false | spl4_35),
% 2.98/0.74    inference(subsumption_resolution,[],[f694,f33])).
% 2.98/0.74  fof(f694,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_35),
% 2.98/0.74    inference(subsumption_resolution,[],[f693,f35])).
% 2.98/0.74  fof(f693,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_35),
% 2.98/0.74    inference(subsumption_resolution,[],[f692,f40])).
% 2.98/0.74  fof(f692,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_35),
% 2.98/0.74    inference(subsumption_resolution,[],[f691,f41])).
% 2.98/0.74  fof(f691,plain,(
% 2.98/0.74    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_35),
% 2.98/0.74    inference(subsumption_resolution,[],[f690,f38])).
% 2.98/0.74  fof(f690,plain,(
% 2.98/0.74    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_35),
% 2.98/0.74    inference(subsumption_resolution,[],[f689,f39])).
% 2.98/0.74  fof(f689,plain,(
% 2.98/0.74    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_35),
% 2.98/0.74    inference(resolution,[],[f684,f61])).
% 2.98/0.74  fof(f684,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) | spl4_35),
% 2.98/0.74    inference(avatar_component_clause,[],[f682])).
% 2.98/0.74  fof(f601,plain,(
% 2.98/0.74    ~spl4_29),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f600])).
% 2.98/0.74  fof(f600,plain,(
% 2.98/0.74    $false | ~spl4_29),
% 2.98/0.74    inference(subsumption_resolution,[],[f599,f33])).
% 2.98/0.74  fof(f599,plain,(
% 2.98/0.74    v2_struct_0(sK0) | ~spl4_29),
% 2.98/0.74    inference(subsumption_resolution,[],[f598,f35])).
% 2.98/0.74  fof(f598,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_29),
% 2.98/0.74    inference(subsumption_resolution,[],[f597,f40])).
% 2.98/0.74  fof(f597,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_29),
% 2.98/0.74    inference(subsumption_resolution,[],[f596,f41])).
% 2.98/0.74  fof(f596,plain,(
% 2.98/0.74    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_29),
% 2.98/0.74    inference(subsumption_resolution,[],[f595,f36])).
% 2.98/0.74  fof(f595,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_29),
% 2.98/0.74    inference(subsumption_resolution,[],[f594,f37])).
% 2.98/0.74  fof(f594,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_29),
% 2.98/0.74    inference(resolution,[],[f421,f60])).
% 2.98/0.74  fof(f421,plain,(
% 2.98/0.74    v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | ~spl4_29),
% 2.98/0.74    inference(avatar_component_clause,[],[f419])).
% 2.98/0.74  fof(f419,plain,(
% 2.98/0.74    spl4_29 <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK1))),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.98/0.74  fof(f536,plain,(
% 2.98/0.74    spl4_31 | spl4_32 | ~spl4_2 | ~spl4_4 | spl4_29 | ~spl4_30),
% 2.98/0.74    inference(avatar_split_clause,[],[f522,f423,f419,f77,f67,f533,f529])).
% 2.98/0.74  fof(f77,plain,(
% 2.98/0.74    spl4_4 <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.98/0.74  fof(f423,plain,(
% 2.98/0.74    spl4_30 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)),
% 2.98/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.98/0.74  fof(f522,plain,(
% 2.98/0.74    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1)) | (~spl4_2 | ~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f521,f39])).
% 2.98/0.74  fof(f521,plain,(
% 2.98/0.74    r1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1)) | (~spl4_2 | ~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f516,f38])).
% 2.98/0.74  fof(f516,plain,(
% 2.98/0.74    v2_struct_0(sK2) | r1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1)) | (~spl4_2 | ~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(resolution,[],[f515,f69])).
% 2.98/0.74  fof(f515,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f514,f33])).
% 2.98/0.74  fof(f514,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f513,f35])).
% 2.98/0.74  fof(f513,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f512,f36])).
% 2.98/0.74  fof(f512,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f511,f37])).
% 2.98/0.74  fof(f511,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f508])).
% 2.98/0.74  fof(f508,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(resolution,[],[f506,f61])).
% 2.98/0.74  fof(f506,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f505,f33])).
% 2.98/0.74  fof(f505,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f504,f35])).
% 2.98/0.74  fof(f504,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f503,f36])).
% 2.98/0.74  fof(f503,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f502,f37])).
% 2.98/0.74  fof(f502,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(duplicate_literal_removal,[],[f501])).
% 2.98/0.74  fof(f501,plain,(
% 2.98/0.74    ( ! [X0] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(resolution,[],[f475,f60])).
% 2.98/0.74  fof(f475,plain,(
% 2.98/0.74    ( ! [X0] : (v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f474,f33])).
% 2.98/0.74  fof(f474,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f473,f34])).
% 2.98/0.74  fof(f473,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f472,f35])).
% 2.98/0.74  fof(f472,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f471,f36])).
% 2.98/0.74  fof(f471,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f470,f37])).
% 2.98/0.74  fof(f470,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f469,f40])).
% 2.98/0.74  fof(f469,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f468,f41])).
% 2.98/0.74  fof(f468,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,X0,sK1)) | r1_tsep_1(sK2,k2_tsep_1(sK0,X0,sK1))) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(resolution,[],[f53,f445])).
% 2.98/0.74  fof(f445,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK2,X0)) ) | (~spl4_4 | spl4_29 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f444,f420])).
% 2.98/0.74  fof(f420,plain,(
% 2.98/0.74    ~v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | spl4_29),
% 2.98/0.74    inference(avatar_component_clause,[],[f419])).
% 2.98/0.74  fof(f444,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK2,X0)) ) | (~spl4_4 | ~spl4_30)),
% 2.98/0.74    inference(subsumption_resolution,[],[f443,f424])).
% 2.98/0.74  fof(f424,plain,(
% 2.98/0.74    m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) | ~spl4_30),
% 2.98/0.74    inference(avatar_component_clause,[],[f423])).
% 2.98/0.74  fof(f443,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK2,X0)) ) | ~spl4_4),
% 2.98/0.74    inference(subsumption_resolution,[],[f442,f38])).
% 2.98/0.74  fof(f442,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK2,X0)) ) | ~spl4_4),
% 2.98/0.74    inference(subsumption_resolution,[],[f440,f39])).
% 2.98/0.74  fof(f440,plain,(
% 2.98/0.74    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK2,X0)) ) | ~spl4_4),
% 2.98/0.74    inference(resolution,[],[f323,f79])).
% 2.98/0.74  fof(f79,plain,(
% 2.98/0.74    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | ~spl4_4),
% 2.98/0.74    inference(avatar_component_clause,[],[f77])).
% 2.98/0.74  fof(f323,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | r1_tsep_1(X1,X2)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f322,f33])).
% 2.98/0.74  fof(f322,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | r1_tsep_1(X1,X2) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(subsumption_resolution,[],[f321,f35])).
% 2.98/0.74  fof(f321,plain,(
% 2.98/0.74    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | r1_tsep_1(X1,X2) | v2_struct_0(sK0)) )),
% 2.98/0.74    inference(resolution,[],[f57,f34])).
% 2.98/0.74  fof(f57,plain,(
% 2.98/0.74    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X3,X1) | v2_struct_0(X0)) )),
% 2.98/0.74    inference(cnf_transformation,[],[f23])).
% 2.98/0.74  fof(f434,plain,(
% 2.98/0.74    spl4_30),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f433])).
% 2.98/0.74  fof(f433,plain,(
% 2.98/0.74    $false | spl4_30),
% 2.98/0.74    inference(subsumption_resolution,[],[f432,f33])).
% 2.98/0.74  fof(f432,plain,(
% 2.98/0.74    v2_struct_0(sK0) | spl4_30),
% 2.98/0.74    inference(subsumption_resolution,[],[f431,f35])).
% 2.98/0.74  fof(f431,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_30),
% 2.98/0.74    inference(subsumption_resolution,[],[f430,f40])).
% 2.98/0.74  fof(f430,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_30),
% 2.98/0.74    inference(subsumption_resolution,[],[f429,f41])).
% 2.98/0.74  fof(f429,plain,(
% 2.98/0.74    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_30),
% 2.98/0.74    inference(subsumption_resolution,[],[f428,f36])).
% 2.98/0.74  fof(f428,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_30),
% 2.98/0.74    inference(subsumption_resolution,[],[f427,f37])).
% 2.98/0.74  fof(f427,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_30),
% 2.98/0.74    inference(resolution,[],[f425,f61])).
% 2.98/0.74  fof(f425,plain,(
% 2.98/0.74    ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) | spl4_30),
% 2.98/0.74    inference(avatar_component_clause,[],[f423])).
% 2.98/0.74  fof(f383,plain,(
% 2.98/0.74    ~spl4_18),
% 2.98/0.74    inference(avatar_contradiction_clause,[],[f382])).
% 2.98/0.74  fof(f382,plain,(
% 2.98/0.74    $false | ~spl4_18),
% 2.98/0.74    inference(subsumption_resolution,[],[f381,f33])).
% 2.98/0.74  fof(f381,plain,(
% 2.98/0.74    v2_struct_0(sK0) | ~spl4_18),
% 2.98/0.74    inference(subsumption_resolution,[],[f380,f35])).
% 2.98/0.74  fof(f380,plain,(
% 2.98/0.74    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_18),
% 2.98/0.74    inference(subsumption_resolution,[],[f379,f36])).
% 2.98/0.74  fof(f379,plain,(
% 2.98/0.74    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_18),
% 2.98/0.74    inference(subsumption_resolution,[],[f378,f37])).
% 2.98/0.74  fof(f378,plain,(
% 2.98/0.74    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_18),
% 2.98/0.74    inference(subsumption_resolution,[],[f377,f40])).
% 2.98/0.74  fof(f377,plain,(
% 2.98/0.74    v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_18),
% 2.98/0.74    inference(subsumption_resolution,[],[f376,f41])).
% 2.98/0.75  fof(f376,plain,(
% 2.98/0.75    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_18),
% 2.98/0.75    inference(resolution,[],[f220,f60])).
% 2.98/0.75  fof(f220,plain,(
% 2.98/0.75    v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | ~spl4_18),
% 2.98/0.75    inference(avatar_component_clause,[],[f218])).
% 2.98/0.75  fof(f233,plain,(
% 2.98/0.75    spl4_19),
% 2.98/0.75    inference(avatar_contradiction_clause,[],[f232])).
% 2.98/0.75  fof(f232,plain,(
% 2.98/0.75    $false | spl4_19),
% 2.98/0.75    inference(subsumption_resolution,[],[f231,f33])).
% 2.98/0.75  fof(f231,plain,(
% 2.98/0.75    v2_struct_0(sK0) | spl4_19),
% 2.98/0.75    inference(subsumption_resolution,[],[f230,f35])).
% 2.98/0.75  fof(f230,plain,(
% 2.98/0.75    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_19),
% 2.98/0.75    inference(subsumption_resolution,[],[f229,f36])).
% 2.98/0.75  fof(f229,plain,(
% 2.98/0.75    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_19),
% 2.98/0.75    inference(subsumption_resolution,[],[f228,f37])).
% 2.98/0.75  fof(f228,plain,(
% 2.98/0.75    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_19),
% 2.98/0.75    inference(subsumption_resolution,[],[f227,f40])).
% 2.98/0.75  fof(f227,plain,(
% 2.98/0.75    v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_19),
% 2.98/0.75    inference(subsumption_resolution,[],[f226,f41])).
% 2.98/0.75  fof(f226,plain,(
% 2.98/0.75    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_19),
% 2.98/0.75    inference(resolution,[],[f224,f61])).
% 2.98/0.75  fof(f224,plain,(
% 2.98/0.75    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | spl4_19),
% 2.98/0.75    inference(avatar_component_clause,[],[f222])).
% 2.98/0.75  fof(f166,plain,(
% 2.98/0.75    spl4_13),
% 2.98/0.75    inference(avatar_contradiction_clause,[],[f165])).
% 2.98/0.75  fof(f165,plain,(
% 2.98/0.75    $false | spl4_13),
% 2.98/0.75    inference(subsumption_resolution,[],[f163,f35])).
% 2.98/0.75  fof(f163,plain,(
% 2.98/0.75    ~l1_pre_topc(sK0) | spl4_13),
% 2.98/0.75    inference(resolution,[],[f161,f37])).
% 2.98/0.75  fof(f161,plain,(
% 2.98/0.75    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl4_13),
% 2.98/0.75    inference(resolution,[],[f155,f48])).
% 2.98/0.75  fof(f155,plain,(
% 2.98/0.75    ~l1_pre_topc(sK1) | spl4_13),
% 2.98/0.75    inference(avatar_component_clause,[],[f153])).
% 2.98/0.75  fof(f113,plain,(
% 2.98/0.75    spl4_8),
% 2.98/0.75    inference(avatar_contradiction_clause,[],[f112])).
% 2.98/0.75  fof(f112,plain,(
% 2.98/0.75    $false | spl4_8),
% 2.98/0.75    inference(subsumption_resolution,[],[f110,f35])).
% 2.98/0.75  fof(f110,plain,(
% 2.98/0.75    ~l1_pre_topc(sK0) | spl4_8),
% 2.98/0.75    inference(resolution,[],[f108,f39])).
% 2.98/0.75  fof(f108,plain,(
% 2.98/0.75    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl4_8),
% 2.98/0.75    inference(resolution,[],[f102,f48])).
% 2.98/0.75  fof(f102,plain,(
% 2.98/0.75    ~l1_pre_topc(sK2) | spl4_8),
% 2.98/0.75    inference(avatar_component_clause,[],[f100])).
% 2.98/0.75  fof(f91,plain,(
% 2.98/0.75    spl4_5 | spl4_6 | spl4_3 | spl4_4),
% 2.98/0.75    inference(avatar_split_clause,[],[f82,f77,f73,f88,f84])).
% 2.98/0.75  fof(f82,plain,(
% 2.98/0.75    r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | (spl4_3 | spl4_4)),
% 2.98/0.75    inference(subsumption_resolution,[],[f81,f74])).
% 2.98/0.75  fof(f74,plain,(
% 2.98/0.75    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | spl4_3),
% 2.98/0.75    inference(avatar_component_clause,[],[f73])).
% 2.98/0.75  fof(f81,plain,(
% 2.98/0.75    r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | spl4_4),
% 2.98/0.75    inference(subsumption_resolution,[],[f46,f78])).
% 2.98/0.75  fof(f78,plain,(
% 2.98/0.75    ~r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | spl4_4),
% 2.98/0.75    inference(avatar_component_clause,[],[f77])).
% 2.98/0.75  fof(f46,plain,(
% 2.98/0.75    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.98/0.75    inference(cnf_transformation,[],[f32])).
% 2.98/0.75  fof(f80,plain,(
% 2.98/0.75    spl4_3 | spl4_4 | spl4_1),
% 2.98/0.75    inference(avatar_split_clause,[],[f71,f63,f77,f73])).
% 2.98/0.75  fof(f71,plain,(
% 2.98/0.75    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | spl4_1),
% 2.98/0.75    inference(subsumption_resolution,[],[f45,f64])).
% 2.98/0.75  fof(f64,plain,(
% 2.98/0.75    ~m1_pre_topc(sK1,sK3) | spl4_1),
% 2.98/0.75    inference(avatar_component_clause,[],[f63])).
% 2.98/0.75  fof(f45,plain,(
% 2.98/0.75    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | m1_pre_topc(sK1,sK3)),
% 2.98/0.75    inference(cnf_transformation,[],[f32])).
% 2.98/0.75  fof(f70,plain,(
% 2.98/0.75    spl4_1 | spl4_2),
% 2.98/0.75    inference(avatar_split_clause,[],[f43,f67,f63])).
% 2.98/0.75  fof(f43,plain,(
% 2.98/0.75    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 2.98/0.75    inference(cnf_transformation,[],[f32])).
% 2.98/0.75  % SZS output end Proof for theBenchmark
% 2.98/0.75  % (3917)------------------------------
% 2.98/0.75  % (3917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.75  % (3917)Termination reason: Refutation
% 2.98/0.75  
% 2.98/0.75  % (3917)Memory used [KB]: 6140
% 2.98/0.75  % (3917)Time elapsed: 0.305 s
% 2.98/0.75  % (3917)------------------------------
% 2.98/0.75  % (3917)------------------------------
% 2.98/0.75  % (3916)Success in time 0.387 s
%------------------------------------------------------------------------------

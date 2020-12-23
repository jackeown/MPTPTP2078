%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:31 EST 2020

% Result     : Theorem 10.31s
% Output     : Refutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :  450 (3152 expanded)
%              Number of leaves         :   64 (1039 expanded)
%              Depth                    :   29
%              Number of atoms          : 2161 (22019 expanded)
%              Number of equality atoms :   95 (2836 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19019,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f245,f246,f443,f464,f2339,f2343,f2385,f2391,f2515,f5064,f5080,f5926,f12653,f12809,f12811,f12831,f12889,f12900,f12909,f13003,f13004,f13012,f13013,f13014,f13015,f13113,f13177,f14208,f14282,f17740,f18448,f18802,f18965,f18975,f19009])).

fof(f19009,plain,
    ( spl16_219
    | ~ spl16_2
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(avatar_split_clause,[],[f6614,f5333,f2185,f242,f12717])).

fof(f12717,plain,
    ( spl16_219
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_219])])).

fof(f242,plain,
    ( spl16_2
  <=> v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f2185,plain,
    ( spl16_34
  <=> ! [X5] : ~ r2_hidden(X5,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).

fof(f5333,plain,
    ( spl16_117
  <=> u1_struct_0(sK7) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_117])])).

fof(f6614,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ spl16_2
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(backward_demodulation,[],[f6458,f6554])).

fof(f6554,plain,
    ( k1_xboole_0 = u1_struct_0(sK7)
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f5335,f4771])).

fof(f4771,plain,
    ( k1_xboole_0 = sK8
    | ~ spl16_34 ),
    inference(resolution,[],[f2186,f173])).

fof(f173,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ( sP3(sK12(X0),X0)
        & r2_hidden(sK12(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f81,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP3(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP3(sK12(X0),X0)
        & r2_hidden(sK12(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP3(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f55,f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f2186,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK8)
    | ~ spl16_34 ),
    inference(avatar_component_clause,[],[f2185])).

fof(f5335,plain,
    ( u1_struct_0(sK7) = sK8
    | ~ spl16_117 ),
    inference(avatar_component_clause,[],[f5333])).

fof(f6458,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_2
    | ~ spl16_34 ),
    inference(backward_demodulation,[],[f255,f4771])).

fof(f255,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_2 ),
    inference(forward_demodulation,[],[f243,f140])).

fof(f140,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,
    ( ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | ~ v5_pre_topc(sK8,sK6,sK7) )
    & ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | v5_pre_topc(sK8,sK6,sK7) )
    & sK8 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f87,f91,f90,f89,f88])).

fof(f88,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK6,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK6,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK6,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK6,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
                | ~ v5_pre_topc(X2,sK6,sK7) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
                | v5_pre_topc(X2,sK6,sK7) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
          & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
              | ~ v5_pre_topc(X2,sK6,sK7) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
              | v5_pre_topc(X2,sK6,sK7) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
        & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
            | ~ v5_pre_topc(sK8,sK6,sK7) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
            | v5_pre_topc(sK8,sK6,sK7) )
          & sK8 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
      & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
          | ~ v5_pre_topc(sK8,sK6,sK7) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
          | v5_pre_topc(sK8,sK6,sK7) )
        & sK8 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
        | ~ v5_pre_topc(sK8,sK6,sK7) )
      & ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
        | v5_pre_topc(sK8,sK6,sK7) )
      & sK8 = sK9
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
      & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f243,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f242])).

fof(f18975,plain,
    ( ~ spl16_220
    | ~ spl16_34
    | spl16_48 ),
    inference(avatar_split_clause,[],[f12659,f2504,f2185,f12744])).

fof(f12744,plain,
    ( spl16_220
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_220])])).

fof(f2504,plain,
    ( spl16_48
  <=> v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).

fof(f12659,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ spl16_34
    | spl16_48 ),
    inference(forward_demodulation,[],[f2505,f4771])).

fof(f2505,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | spl16_48 ),
    inference(avatar_component_clause,[],[f2504])).

fof(f18965,plain,
    ( spl16_117
    | ~ spl16_4
    | ~ spl16_116 ),
    inference(avatar_split_clause,[],[f13426,f5329,f287,f5333])).

fof(f287,plain,
    ( spl16_4
  <=> r1_tarski(sK8,u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f5329,plain,
    ( spl16_116
  <=> r1_tarski(u1_struct_0(sK7),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_116])])).

fof(f13426,plain,
    ( u1_struct_0(sK7) = sK8
    | ~ spl16_4
    | ~ spl16_116 ),
    inference(subsumption_resolution,[],[f13417,f289])).

fof(f289,plain,
    ( r1_tarski(sK8,u1_struct_0(sK7))
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f287])).

fof(f13417,plain,
    ( u1_struct_0(sK7) = sK8
    | ~ r1_tarski(sK8,u1_struct_0(sK7))
    | ~ spl16_116 ),
    inference(resolution,[],[f5330,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5330,plain,
    ( r1_tarski(u1_struct_0(sK7),sK8)
    | ~ spl16_116 ),
    inference(avatar_component_clause,[],[f5329])).

fof(f18802,plain,
    ( ~ spl16_232
    | spl16_3
    | spl16_104
    | ~ spl16_227 ),
    inference(avatar_split_clause,[],[f18801,f12968,f5068,f283,f12996])).

fof(f12996,plain,
    ( spl16_232
  <=> v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_232])])).

fof(f283,plain,
    ( spl16_3
  <=> v1_xboole_0(u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f5068,plain,
    ( spl16_104
  <=> v1_partfun1(sK8,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_104])])).

fof(f12968,plain,
    ( spl16_227
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_227])])).

fof(f18801,plain,
    ( v1_partfun1(sK8,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK7))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f13279,f12969])).

fof(f12969,plain,
    ( v1_funct_1(sK8)
    | ~ spl16_227 ),
    inference(avatar_component_clause,[],[f12968])).

fof(f13279,plain,
    ( ~ v1_funct_1(sK8)
    | v1_partfun1(sK8,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK7))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(resolution,[],[f269,f1991])).

fof(f1991,plain,(
    ! [X17,X18,X16] :
      ( ~ r1_tarski(X16,k2_zfmisc_1(X17,X18))
      | ~ v1_funct_1(X16)
      | v1_partfun1(X16,X17)
      | v1_xboole_0(X18)
      | ~ v1_funct_2(X16,X17,X18) ) ),
    inference(resolution,[],[f176,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f269,plain,(
    r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))) ),
    inference(resolution,[],[f201,f136])).

fof(f136,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f92])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f18448,plain,
    ( spl16_43
    | ~ spl16_143
    | ~ spl16_227 ),
    inference(avatar_contradiction_clause,[],[f18447])).

fof(f18447,plain,
    ( $false
    | spl16_43
    | ~ spl16_143
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f18446,f859])).

% (10240)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
fof(f859,plain,(
    v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(resolution,[],[f215,f259])).

fof(f259,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    inference(forward_demodulation,[],[f139,f140])).

fof(f139,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    inference(cnf_transformation,[],[f92])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f18446,plain,
    ( ~ v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_43
    | ~ spl16_143
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f18445,f446])).

fof(f446,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f212,f136])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f18445,plain,
    ( ~ v1_relat_1(sK8)
    | ~ v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_43
    | ~ spl16_143
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f18443,f12969])).

fof(f18443,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_43
    | ~ spl16_143 ),
    inference(resolution,[],[f18427,f1271])).

fof(f1271,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f1265])).

fof(f1265,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f186,f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP4(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f62,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f18427,plain,
    ( ~ sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8)
    | spl16_43
    | ~ spl16_143 ),
    inference(resolution,[],[f17700,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f82])).

fof(f17700,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | spl16_43
    | ~ spl16_143 ),
    inference(forward_demodulation,[],[f2380,f6091])).

fof(f6091,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK8)
    | ~ spl16_143 ),
    inference(avatar_component_clause,[],[f6089])).

fof(f6089,plain,
    ( spl16_143
  <=> u1_struct_0(sK6) = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_143])])).

fof(f2380,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | spl16_43 ),
    inference(avatar_component_clause,[],[f2378])).

fof(f2378,plain,
    ( spl16_43
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_43])])).

fof(f17740,plain,
    ( ~ spl16_3
    | spl16_116 ),
    inference(avatar_split_clause,[],[f5358,f5329,f283])).

fof(f5358,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK7))
    | spl16_116 ),
    inference(resolution,[],[f5331,f422])).

fof(f422,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f193,f169])).

fof(f169,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK11(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f103,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK11(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f193,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f117,f118])).

fof(f118,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f5331,plain,
    ( ~ r1_tarski(u1_struct_0(sK7),sK8)
    | spl16_116 ),
    inference(avatar_component_clause,[],[f5329])).

fof(f14282,plain,
    ( spl16_143
    | ~ spl16_142 ),
    inference(avatar_split_clause,[],[f14281,f6085,f6089])).

fof(f6085,plain,
    ( spl16_142
  <=> r1_tarski(u1_struct_0(sK6),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_142])])).

fof(f14281,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK8)
    | ~ spl16_142 ),
    inference(subsumption_resolution,[],[f14280,f446])).

fof(f14280,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl16_142 ),
    inference(subsumption_resolution,[],[f14268,f818])).

fof(f818,plain,(
    v4_relat_1(sK8,u1_struct_0(sK6)) ),
    inference(resolution,[],[f214,f136])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f14268,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK8)
    | ~ v4_relat_1(sK8,u1_struct_0(sK6))
    | ~ v1_relat_1(sK8)
    | ~ spl16_142 ),
    inference(resolution,[],[f6086,f642])).

fof(f642,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(X4))
      | k1_relat_1(X4) = X3
      | ~ v4_relat_1(X4,X3)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f191,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f6086,plain,
    ( r1_tarski(u1_struct_0(sK6),k1_relat_1(sK8))
    | ~ spl16_142 ),
    inference(avatar_component_clause,[],[f6085])).

fof(f14208,plain,
    ( ~ spl16_104
    | spl16_142 ),
    inference(avatar_contradiction_clause,[],[f14207])).

fof(f14207,plain,
    ( $false
    | ~ spl16_104
    | spl16_142 ),
    inference(subsumption_resolution,[],[f14174,f5873])).

fof(f5873,plain,(
    v4_relat_1(sK8,k1_relat_1(sK8)) ),
    inference(resolution,[],[f5857,f228])).

fof(f228,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f115])).

fof(f5857,plain,(
    ! [X21] :
      ( ~ r1_tarski(k1_relat_1(sK8),X21)
      | v4_relat_1(sK8,X21) ) ),
    inference(resolution,[],[f1953,f136])).

fof(f1953,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ r1_tarski(k1_relat_1(X4),X5)
      | v4_relat_1(X4,X5) ) ),
    inference(resolution,[],[f220,f214])).

fof(f220,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f14174,plain,
    ( ~ v4_relat_1(sK8,k1_relat_1(sK8))
    | ~ spl16_104
    | spl16_142 ),
    inference(resolution,[],[f13351,f6087])).

fof(f6087,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k1_relat_1(sK8))
    | spl16_142 ),
    inference(avatar_component_clause,[],[f6085])).

fof(f13351,plain,
    ( ! [X1] :
        ( r1_tarski(u1_struct_0(sK6),X1)
        | ~ v4_relat_1(sK8,X1) )
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f13350,f818])).

fof(f13350,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(sK8,X1)
        | r1_tarski(u1_struct_0(sK6),X1)
        | ~ v4_relat_1(sK8,u1_struct_0(sK6)) )
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f13239,f446])).

fof(f13239,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(sK8,X1)
        | ~ v1_relat_1(sK8)
        | r1_tarski(u1_struct_0(sK6),X1)
        | ~ v4_relat_1(sK8,u1_struct_0(sK6)) )
    | ~ spl16_104 ),
    inference(resolution,[],[f5070,f1550])).

fof(f1550,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_partfun1(X7,X8)
      | ~ v4_relat_1(X7,X9)
      | ~ v1_relat_1(X7)
      | r1_tarski(X8,X9)
      | ~ v4_relat_1(X7,X8) ) ),
    inference(duplicate_literal_removal,[],[f1538])).

fof(f1538,plain,(
    ! [X8,X7,X9] :
      ( r1_tarski(X8,X9)
      | ~ v4_relat_1(X7,X9)
      | ~ v1_relat_1(X7)
      | ~ v1_partfun1(X7,X8)
      | ~ v4_relat_1(X7,X8)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f179,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f5070,plain,
    ( v1_partfun1(sK8,u1_struct_0(sK6))
    | ~ spl16_104 ),
    inference(avatar_component_clause,[],[f5068])).

fof(f13177,plain,
    ( ~ spl16_41
    | ~ spl16_39
    | ~ spl16_42
    | ~ spl16_43
    | ~ spl16_228
    | spl16_229
    | ~ spl16_44
    | ~ spl16_227 ),
    inference(avatar_split_clause,[],[f13176,f12968,f2382,f12976,f12972,f2378,f2374,f2323,f2370])).

fof(f2370,plain,
    ( spl16_41
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).

fof(f2323,plain,
    ( spl16_39
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).

fof(f2374,plain,
    ( spl16_42
  <=> v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).

fof(f12972,plain,
    ( spl16_228
  <=> v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_228])])).

fof(f12976,plain,
    ( spl16_229
  <=> v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_229])])).

fof(f2382,plain,
    ( spl16_44
  <=> v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).

fof(f13176,plain,
    ( ~ v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f13175,f130])).

fof(f130,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f13175,plain,
    ( ~ v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(sK6)
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f13174,f131])).

fof(f131,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f13174,plain,
    ( ~ v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_227 ),
    inference(subsumption_resolution,[],[f13135,f12969])).

fof(f13135,plain,
    ( ~ v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[],[f259,f233])).

fof(f233,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f13113,plain,
    ( ~ spl16_229
    | spl16_2 ),
    inference(avatar_split_clause,[],[f13112,f242,f12976])).

fof(f13112,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | spl16_2 ),
    inference(forward_demodulation,[],[f244,f140])).

fof(f244,plain,
    ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | spl16_2 ),
    inference(avatar_component_clause,[],[f242])).

fof(f13015,plain,(
    spl16_227 ),
    inference(avatar_split_clause,[],[f134,f12968])).

fof(f134,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f92])).

fof(f13014,plain,(
    spl16_232 ),
    inference(avatar_split_clause,[],[f135,f12996])).

fof(f135,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f92])).

fof(f13013,plain,(
    spl16_233 ),
    inference(avatar_split_clause,[],[f136,f13000])).

fof(f13000,plain,
    ( spl16_233
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_233])])).

fof(f13012,plain,(
    spl16_228 ),
    inference(avatar_split_clause,[],[f256,f12972])).

fof(f256,plain,(
    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(forward_demodulation,[],[f138,f140])).

fof(f138,plain,(
    v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(cnf_transformation,[],[f92])).

fof(f13004,plain,
    ( ~ spl16_232
    | ~ spl16_233
    | ~ spl16_227
    | ~ spl16_42
    | spl16_44
    | ~ spl16_1
    | ~ spl16_43 ),
    inference(avatar_split_clause,[],[f12695,f2378,f238,f2382,f2374,f12968,f13000,f12996])).

fof(f238,plain,
    ( spl16_1
  <=> v5_pre_topc(sK8,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f12695,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f12694,f130])).

fof(f12694,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f12693,f131])).

fof(f12693,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f12692,f132])).

fof(f132,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f12692,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f6166,f133])).

fof(f133,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f6166,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43 ),
    inference(resolution,[],[f2379,f235])).

fof(f235,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f2379,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ spl16_43 ),
    inference(avatar_component_clause,[],[f2378])).

fof(f13003,plain,
    ( ~ spl16_232
    | ~ spl16_233
    | ~ spl16_227
    | ~ spl16_42
    | spl16_1
    | ~ spl16_43
    | ~ spl16_44 ),
    inference(avatar_split_clause,[],[f12702,f2382,f2378,f238,f2374,f12968,f13000,f12996])).

fof(f12702,plain,
    ( v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_43
    | ~ spl16_44 ),
    inference(subsumption_resolution,[],[f12701,f130])).

fof(f12701,plain,
    ( v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43
    | ~ spl16_44 ),
    inference(subsumption_resolution,[],[f12700,f131])).

fof(f12700,plain,
    ( v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43
    | ~ spl16_44 ),
    inference(subsumption_resolution,[],[f12699,f132])).

fof(f12699,plain,
    ( v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43
    | ~ spl16_44 ),
    inference(subsumption_resolution,[],[f6180,f133])).

fof(f6180,plain,
    ( v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43
    | ~ spl16_44 ),
    inference(subsumption_resolution,[],[f6165,f2384])).

fof(f2384,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_44 ),
    inference(avatar_component_clause,[],[f2382])).

fof(f6165,plain,
    ( ~ v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_43 ),
    inference(resolution,[],[f2379,f236])).

fof(f236,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f12909,plain,
    ( spl16_221
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(avatar_split_clause,[],[f6615,f5333,f2185,f12842])).

fof(f12842,plain,
    ( spl16_221
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_221])])).

fof(f6615,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(backward_demodulation,[],[f6459,f6554])).

fof(f6459,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ spl16_34 ),
    inference(backward_demodulation,[],[f256,f4771])).

fof(f12900,plain,
    ( ~ spl16_219
    | spl16_220
    | ~ spl16_221
    | ~ spl16_22
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(avatar_split_clause,[],[f12899,f5333,f2492,f2319,f2185,f405,f401,f12842,f12744,f12717])).

fof(f401,plain,
    ( spl16_22
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f405,plain,
    ( spl16_23
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).

fof(f2319,plain,
    ( spl16_38
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f2492,plain,
    ( spl16_45
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f12899,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ spl16_22
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12898,f1005])).

fof(f1005,plain,
    ( ! [X5] : v1_funct_2(k1_xboole_0,X5,k1_xboole_0)
    | ~ spl16_22 ),
    inference(superposition,[],[f211,f980])).

fof(f980,plain,
    ( ! [X3] : k1_xboole_0 = sK15(X3,k1_xboole_0)
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f974,f845])).

fof(f845,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f556,f833])).

fof(f833,plain,(
    ! [X4] : v4_relat_1(k1_xboole_0,X4) ),
    inference(resolution,[],[f826,f702])).

fof(f702,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f698,f143])).

fof(f143,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f698,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f431,f670])).

fof(f670,plain,(
    ! [X8,X9] :
      ( sK15(X8,X9) = X8
      | ~ v1_xboole_0(X8) ) ),
    inference(subsumption_resolution,[],[f647,f422])).

fof(f647,plain,(
    ! [X8,X9] :
      ( sK15(X8,X9) = X8
      | ~ r1_tarski(X8,sK15(X8,X9))
      | ~ v1_xboole_0(X8) ) ),
    inference(resolution,[],[f191,f499])).

fof(f499,plain,(
    ! [X2,X1] :
      ( r1_tarski(sK15(X1,X2),X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f427,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f232,f155])).

fof(f155,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f232,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f427,plain,(
    ! [X2,X3] : r1_tarski(sK15(X2,X3),k2_zfmisc_1(X2,X3)) ),
    inference(resolution,[],[f206,f201])).

fof(f206,plain,(
    ! [X0,X1] : m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK15(X0,X1),X0,X1)
      & v1_funct_1(sK15(X0,X1))
      & v5_relat_1(sK15(X0,X1),X1)
      & v4_relat_1(sK15(X0,X1),X0)
      & v1_relat_1(sK15(X0,X1))
      & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f25,f128])).

fof(f128,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK15(X0,X1),X0,X1)
        & v1_funct_1(sK15(X0,X1))
        & v5_relat_1(sK15(X0,X1),X1)
        & v4_relat_1(sK15(X0,X1),X0)
        & v1_relat_1(sK15(X0,X1))
        & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f431,plain,(
    ! [X5] : m1_subset_1(sK15(k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f206,f232])).

fof(f826,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f214,f231])).

fof(f231,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f127])).

fof(f556,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k1_xboole_0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f554,f402])).

fof(f402,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f401])).

fof(f554,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ v4_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f179,f144])).

fof(f144,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f974,plain,(
    ! [X3] :
      ( k1_xboole_0 = sK15(X3,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,sK15(X3,k1_xboole_0)) ) ),
    inference(resolution,[],[f459,f191])).

fof(f459,plain,(
    ! [X1] : r1_tarski(sK15(X1,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f428,f201])).

fof(f428,plain,(
    ! [X0] : m1_subset_1(sK15(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f206,f231])).

fof(f211,plain,(
    ! [X0,X1] : v1_funct_2(sK15(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f129])).

fof(f12898,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12897,f4771])).

fof(f12897,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12896,f6554])).

fof(f12896,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12895,f702])).

fof(f12895,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12894,f4771])).

fof(f12894,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12893,f231])).

fof(f12893,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12892,f6554])).

fof(f12892,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12891,f406])).

fof(f406,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl16_23 ),
    inference(avatar_component_clause,[],[f405])).

fof(f12891,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12890,f4771])).

fof(f12890,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12729,f4771])).

fof(f12729,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12728,f6554])).

fof(f12728,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12727,f4771])).

fof(f12727,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12726,f4771])).

fof(f12726,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12725,f6554])).

fof(f12725,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_38
    | ~ spl16_45 ),
    inference(subsumption_resolution,[],[f12724,f2493])).

fof(f2493,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_45 ),
    inference(avatar_component_clause,[],[f2492])).

fof(f12724,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f12723,f2320])).

fof(f2320,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_38 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f12723,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(subsumption_resolution,[],[f12722,f132])).

fof(f12722,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(subsumption_resolution,[],[f2478,f133])).

fof(f2478,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(resolution,[],[f236,f259])).

fof(f12889,plain,
    ( ~ spl16_220
    | spl16_219
    | ~ spl16_221
    | ~ spl16_22
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(avatar_split_clause,[],[f12888,f5333,f2492,f2319,f2185,f405,f401,f12842,f12717,f12744])).

fof(f12888,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ spl16_22
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12887,f1005])).

fof(f12887,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12886,f4771])).

fof(f12886,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12885,f6554])).

fof(f12885,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12884,f702])).

fof(f12884,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12883,f4771])).

fof(f12883,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12882,f231])).

fof(f12882,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12881,f6554])).

fof(f12881,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_23
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12880,f406])).

fof(f12880,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12879,f4771])).

fof(f12879,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12755,f4771])).

fof(f12755,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12754,f6554])).

fof(f12754,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12753,f4771])).

fof(f12753,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12752,f6554])).

fof(f12752,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_38
    | ~ spl16_45 ),
    inference(forward_demodulation,[],[f12751,f4771])).

fof(f12751,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ spl16_38
    | ~ spl16_45 ),
    inference(subsumption_resolution,[],[f12750,f2493])).

fof(f12750,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f12749,f2320])).

fof(f12749,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(subsumption_resolution,[],[f12748,f132])).

fof(f12748,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(subsumption_resolution,[],[f2426,f133])).

fof(f2426,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(resolution,[],[f235,f259])).

fof(f12831,plain,
    ( ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(avatar_contradiction_clause,[],[f12830])).

fof(f12830,plain,
    ( $false
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12829,f1005])).

fof(f12829,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK6),k1_xboole_0)
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12828,f980])).

fof(f12828,plain,
    ( ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),u1_struct_0(sK6),k1_xboole_0)
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12827,f6554])).

fof(f12827,plain,
    ( ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12826,f702])).

fof(f12826,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12825,f980])).

fof(f12825,plain,
    ( ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12824,f231])).

fof(f12824,plain,
    ( ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0)))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12823,f6554])).

fof(f12823,plain,
    ( ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12822,f143])).

fof(f12822,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12821,f980])).

fof(f12821,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_117
    | ~ spl16_217
    | spl16_220 ),
    inference(forward_demodulation,[],[f12820,f6554])).

fof(f12820,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_217
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12819,f12813])).

fof(f12813,plain,
    ( ! [X0] :
        ( v5_pre_topc(X0,sK6,sK7)
        | ~ v1_xboole_0(X0) )
    | ~ spl16_217 ),
    inference(superposition,[],[f12688,f155])).

fof(f12688,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,sK7)
    | ~ spl16_217 ),
    inference(avatar_component_clause,[],[f12687])).

fof(f12687,plain,
    ( spl16_217
  <=> v5_pre_topc(k1_xboole_0,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_217])])).

fof(f12819,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12818,f130])).

fof(f12818,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK6)
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12817,f131])).

fof(f12817,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12816,f132])).

fof(f12816,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl16_220 ),
    inference(subsumption_resolution,[],[f12815,f133])).

fof(f12815,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl16_220 ),
    inference(resolution,[],[f12814,f2351])).

fof(f2351,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1)
      | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2350,f210])).

fof(f210,plain,(
    ! [X0,X1] : v1_funct_1(sK15(X0,X1)) ),
    inference(cnf_transformation,[],[f129])).

fof(f2350,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1)
      | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))
      | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2345,f211])).

fof(f2345,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1)
      | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))
      | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f233,f206])).

fof(f12814,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
        | ~ v1_xboole_0(X0) )
    | spl16_220 ),
    inference(superposition,[],[f12745,f155])).

fof(f12745,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | spl16_220 ),
    inference(avatar_component_clause,[],[f12744])).

fof(f12811,plain,
    ( spl16_217
    | ~ spl16_1
    | ~ spl16_34 ),
    inference(avatar_split_clause,[],[f12810,f2185,f238,f12687])).

fof(f12810,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,sK7)
    | ~ spl16_1
    | ~ spl16_34 ),
    inference(forward_demodulation,[],[f239,f4771])).

fof(f239,plain,
    ( v5_pre_topc(sK8,sK6,sK7)
    | ~ spl16_1 ),
    inference(avatar_component_clause,[],[f238])).

fof(f12809,plain,
    ( ~ spl16_219
    | spl16_2
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(avatar_split_clause,[],[f12808,f5333,f2185,f242,f12717])).

fof(f12808,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | spl16_2
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12807,f6456])).

fof(f6456,plain,
    ( k1_xboole_0 = sK9
    | ~ spl16_34 ),
    inference(backward_demodulation,[],[f140,f4771])).

fof(f12807,plain,
    ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))
    | spl16_2
    | ~ spl16_34
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f244,f6554])).

fof(f12653,plain,
    ( spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(avatar_contradiction_clause,[],[f12652])).

fof(f12652,plain,
    ( $false
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12651,f1005])).

fof(f12651,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK6),k1_xboole_0)
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12650,f980])).

fof(f12650,plain,
    ( ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),u1_struct_0(sK6),k1_xboole_0)
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12649,f6554])).

fof(f12649,plain,
    ( ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12648,f702])).

fof(f12648,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12647,f980])).

fof(f12647,plain,
    ( ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12646,f231])).

fof(f12646,plain,
    ( ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0)))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12645,f6554])).

fof(f12645,plain,
    ( ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f12644,f143])).

fof(f12644,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_22
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12643,f980])).

fof(f12643,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_34
    | ~ spl16_48
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f12642,f6554])).

fof(f12642,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | spl16_1
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f12641,f6542])).

fof(f6542,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK6,sK7)
        | ~ v1_xboole_0(X0) )
    | spl16_1
    | ~ spl16_34 ),
    inference(superposition,[],[f6457,f155])).

fof(f6457,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK6,sK7)
    | spl16_1
    | ~ spl16_34 ),
    inference(backward_demodulation,[],[f240,f4771])).

fof(f240,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f238])).

fof(f12641,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f12640,f130])).

fof(f12640,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK6)
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f12639,f131])).

fof(f12639,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f12638,f132])).

fof(f12638,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f12637,f133])).

fof(f12637,plain,
    ( ~ v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))
    | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7)
    | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(resolution,[],[f6976,f2387])).

fof(f2387,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1)
      | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2386,f210])).

fof(f2386,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1)
      | ~ v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))
      | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2358,f211])).

fof(f2358,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1)
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))
      | ~ m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f234,f206])).

fof(f234,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f6976,plain,
    ( ! [X0] :
        ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
        | ~ v1_xboole_0(X0) )
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(superposition,[],[f6484,f155])).

fof(f6484,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ spl16_34
    | ~ spl16_48 ),
    inference(backward_demodulation,[],[f2506,f4771])).

fof(f2506,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ spl16_48 ),
    inference(avatar_component_clause,[],[f2504])).

fof(f5926,plain,
    ( spl16_42
    | ~ spl16_104 ),
    inference(avatar_contradiction_clause,[],[f5925])).

fof(f5925,plain,
    ( $false
    | spl16_42
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f5924,f859])).

fof(f5924,plain,
    ( ~ v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_42
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f5923,f446])).

fof(f5923,plain,
    ( ~ v1_relat_1(sK8)
    | ~ v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_42
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f5921,f134])).

fof(f5921,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_42
    | ~ spl16_104 ),
    inference(resolution,[],[f5712,f1271])).

fof(f5712,plain,
    ( ~ sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8)
    | spl16_42
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f5711,f818])).

fof(f5711,plain,
    ( ~ sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8)
    | ~ v4_relat_1(sK8,u1_struct_0(sK6))
    | spl16_42
    | ~ spl16_104 ),
    inference(subsumption_resolution,[],[f5709,f5070])).

fof(f5709,plain,
    ( ~ sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8)
    | ~ v1_partfun1(sK8,u1_struct_0(sK6))
    | ~ v4_relat_1(sK8,u1_struct_0(sK6))
    | spl16_42 ),
    inference(resolution,[],[f1562,f2376])).

fof(f2376,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | spl16_42 ),
    inference(avatar_component_clause,[],[f2374])).

fof(f1562,plain,(
    ! [X14,X15,X13] :
      ( v1_funct_2(X13,X14,X15)
      | ~ sP4(X15,X13)
      | ~ v1_partfun1(X13,X14)
      | ~ v4_relat_1(X13,X14) ) ),
    inference(subsumption_resolution,[],[f1540,f1228])).

fof(f1228,plain,(
    ! [X4,X5] :
      ( ~ sP4(X4,X5)
      | v1_relat_1(X5) ) ),
    inference(resolution,[],[f185,f212])).

fof(f1540,plain,(
    ! [X14,X15,X13] :
      ( v1_funct_2(X13,X14,X15)
      | ~ sP4(X15,X13)
      | ~ v1_partfun1(X13,X14)
      | ~ v4_relat_1(X13,X14)
      | ~ v1_relat_1(X13) ) ),
    inference(superposition,[],[f184,f187])).

fof(f184,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f5080,plain,
    ( ~ spl16_3
    | spl16_34 ),
    inference(avatar_split_clause,[],[f5079,f2185,f283])).

fof(f5079,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK8)
      | ~ v1_xboole_0(u1_struct_0(sK7)) ) ),
    inference(subsumption_resolution,[],[f732,f169])).

fof(f732,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK7))
      | ~ r2_hidden(X1,sK8)
      | ~ v1_xboole_0(u1_struct_0(sK7)) ) ),
    inference(superposition,[],[f720,f253])).

fof(f253,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f231,f155])).

fof(f720,plain,(
    ! [X13] :
      ( r2_hidden(X13,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))
      | ~ r2_hidden(X13,sK8) ) ),
    inference(resolution,[],[f192,f269])).

fof(f192,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f5064,plain,
    ( ~ spl16_3
    | spl16_4 ),
    inference(avatar_split_clause,[],[f2541,f287,f283])).

fof(f2541,plain,
    ( r1_tarski(sK8,u1_struct_0(sK7))
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(superposition,[],[f269,f253])).

fof(f2515,plain,(
    spl16_45 ),
    inference(avatar_contradiction_clause,[],[f2514])).

fof(f2514,plain,
    ( $false
    | spl16_45 ),
    inference(subsumption_resolution,[],[f2513,f130])).

fof(f2513,plain,
    ( ~ v2_pre_topc(sK6)
    | spl16_45 ),
    inference(subsumption_resolution,[],[f2512,f131])).

fof(f2512,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl16_45 ),
    inference(resolution,[],[f2494,f163])).

fof(f163,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f2494,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl16_45 ),
    inference(avatar_component_clause,[],[f2492])).

fof(f2391,plain,(
    spl16_41 ),
    inference(avatar_contradiction_clause,[],[f2390])).

fof(f2390,plain,
    ( $false
    | spl16_41 ),
    inference(subsumption_resolution,[],[f2389,f132])).

fof(f2389,plain,
    ( ~ v2_pre_topc(sK7)
    | spl16_41 ),
    inference(subsumption_resolution,[],[f2388,f133])).

fof(f2388,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | spl16_41 ),
    inference(resolution,[],[f2372,f163])).

fof(f2372,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | spl16_41 ),
    inference(avatar_component_clause,[],[f2370])).

fof(f2385,plain,
    ( ~ spl16_41
    | ~ spl16_42
    | ~ spl16_43
    | spl16_44
    | ~ spl16_2
    | ~ spl16_39 ),
    inference(avatar_split_clause,[],[f2368,f2323,f242,f2382,f2378,f2374,f2370])).

fof(f2368,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_2
    | ~ spl16_39 ),
    inference(subsumption_resolution,[],[f2367,f130])).

fof(f2367,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(sK6)
    | ~ spl16_2
    | ~ spl16_39 ),
    inference(subsumption_resolution,[],[f2366,f131])).

fof(f2366,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_2
    | ~ spl16_39 ),
    inference(subsumption_resolution,[],[f2365,f2324])).

fof(f2324,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ spl16_39 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f2365,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f2364,f134])).

fof(f2364,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f2363,f256])).

fof(f2363,plain,
    ( v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f2357,f255])).

fof(f2357,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[],[f234,f259])).

fof(f2343,plain,(
    spl16_39 ),
    inference(avatar_contradiction_clause,[],[f2342])).

fof(f2342,plain,
    ( $false
    | spl16_39 ),
    inference(subsumption_resolution,[],[f2340,f133])).

fof(f2340,plain,
    ( ~ l1_pre_topc(sK7)
    | spl16_39 ),
    inference(resolution,[],[f2325,f614])).

fof(f614,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f182,f147])).

fof(f147,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f2325,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | spl16_39 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f2339,plain,(
    spl16_38 ),
    inference(avatar_contradiction_clause,[],[f2338])).

fof(f2338,plain,
    ( $false
    | spl16_38 ),
    inference(subsumption_resolution,[],[f2336,f131])).

fof(f2336,plain,
    ( ~ l1_pre_topc(sK6)
    | spl16_38 ),
    inference(resolution,[],[f2321,f614])).

fof(f2321,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl16_38 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f464,plain,(
    spl16_23 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl16_23 ),
    inference(subsumption_resolution,[],[f462,f143])).

fof(f462,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl16_23 ),
    inference(subsumption_resolution,[],[f458,f456])).

fof(f456,plain,
    ( ! [X0,X1] : ~ v1_xboole_0(sK15(X0,X1))
    | spl16_23 ),
    inference(resolution,[],[f445,f210])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_xboole_0(X0) )
    | spl16_23 ),
    inference(superposition,[],[f407,f155])).

fof(f407,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl16_23 ),
    inference(avatar_component_clause,[],[f405])).

fof(f458,plain,(
    ! [X0] :
      ( v1_xboole_0(sK15(X0,k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f428,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f443,plain,(
    spl16_22 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl16_22 ),
    inference(subsumption_resolution,[],[f437,f143])).

fof(f437,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl16_22 ),
    inference(superposition,[],[f433,f232])).

fof(f433,plain,
    ( ! [X0,X1] : ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
    | spl16_22 ),
    inference(subsumption_resolution,[],[f426,f414])).

fof(f414,plain,
    ( ! [X0,X1] : ~ v1_xboole_0(sK15(X0,X1))
    | spl16_22 ),
    inference(resolution,[],[f409,f207])).

fof(f207,plain,(
    ! [X0,X1] : v1_relat_1(sK15(X0,X1)) ),
    inference(cnf_transformation,[],[f129])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | spl16_22 ),
    inference(superposition,[],[f403,f155])).

fof(f403,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl16_22 ),
    inference(avatar_component_clause,[],[f401])).

fof(f426,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK15(X0,X1))
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f206,f157])).

fof(f246,plain,
    ( spl16_1
    | spl16_2 ),
    inference(avatar_split_clause,[],[f141,f242,f238])).

fof(f141,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f245,plain,
    ( ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f142,f242,f238])).

fof(f142,plain,
    ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:22:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (9957)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (9958)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (9977)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (9969)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (9961)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (9960)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (9980)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (9967)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (9955)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (9966)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (9956)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (9959)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (9983)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (9954)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (9982)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (9981)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (9974)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (9962)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (9972)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (9973)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (9979)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (9971)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.56  % (9978)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.56  % (9963)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.56  % (9965)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (9970)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.56  % (9964)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.56  % (9975)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.56  % (9971)Refutation not found, incomplete strategy% (9971)------------------------------
% 1.39/0.56  % (9971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9971)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9971)Memory used [KB]: 10746
% 1.39/0.56  % (9971)Time elapsed: 0.148 s
% 1.39/0.56  % (9971)------------------------------
% 1.39/0.56  % (9971)------------------------------
% 1.39/0.57  % (9976)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.57  % (9964)Refutation not found, incomplete strategy% (9964)------------------------------
% 1.39/0.57  % (9964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (9964)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (9964)Memory used [KB]: 10874
% 1.39/0.57  % (9964)Time elapsed: 0.162 s
% 1.39/0.57  % (9964)------------------------------
% 1.39/0.57  % (9964)------------------------------
% 1.39/0.57  % (9968)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.58  % (9963)Refutation not found, incomplete strategy% (9963)------------------------------
% 1.61/0.58  % (9963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (9963)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (9963)Memory used [KB]: 10874
% 1.61/0.58  % (9963)Time elapsed: 0.156 s
% 1.61/0.58  % (9963)------------------------------
% 1.61/0.58  % (9963)------------------------------
% 1.61/0.59  % (9965)Refutation not found, incomplete strategy% (9965)------------------------------
% 1.61/0.59  % (9965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (9965)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (9965)Memory used [KB]: 10874
% 1.61/0.59  % (9965)Time elapsed: 0.167 s
% 1.61/0.59  % (9965)------------------------------
% 1.61/0.59  % (9965)------------------------------
% 1.61/0.60  % (9954)Refutation not found, incomplete strategy% (9954)------------------------------
% 1.61/0.60  % (9954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (9954)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.60  
% 1.61/0.60  % (9954)Memory used [KB]: 2046
% 1.61/0.60  % (9954)Time elapsed: 0.177 s
% 1.61/0.60  % (9954)------------------------------
% 1.61/0.60  % (9954)------------------------------
% 2.23/0.69  % (9995)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.60/0.73  % (9996)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.60/0.74  % (9998)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.60/0.74  % (9997)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.60/0.75  % (9999)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.39/0.84  % (9959)Time limit reached!
% 3.39/0.84  % (9959)------------------------------
% 3.39/0.84  % (9959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.84  % (9959)Termination reason: Time limit
% 3.39/0.84  
% 3.39/0.84  % (9959)Memory used [KB]: 8699
% 3.39/0.84  % (9959)Time elapsed: 0.426 s
% 3.39/0.84  % (9959)------------------------------
% 3.39/0.84  % (9959)------------------------------
% 3.61/0.90  % (9996)Refutation not found, incomplete strategy% (9996)------------------------------
% 3.61/0.90  % (9996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.90  % (9996)Termination reason: Refutation not found, incomplete strategy
% 3.61/0.90  
% 3.61/0.90  % (9996)Memory used [KB]: 6268
% 3.61/0.90  % (9996)Time elapsed: 0.278 s
% 3.61/0.90  % (9996)------------------------------
% 3.61/0.90  % (9996)------------------------------
% 3.61/0.93  % (9955)Time limit reached!
% 3.61/0.93  % (9955)------------------------------
% 3.61/0.93  % (9955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.93  % (9955)Termination reason: Time limit
% 4.11/0.93  
% 4.11/0.93  % (9955)Memory used [KB]: 7291
% 4.11/0.93  % (9955)Time elapsed: 0.519 s
% 4.11/0.93  % (9955)------------------------------
% 4.11/0.93  % (9955)------------------------------
% 4.11/0.94  % (9966)Time limit reached!
% 4.11/0.94  % (9966)------------------------------
% 4.11/0.94  % (9966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.96  % (9966)Termination reason: Time limit
% 4.26/0.96  % (9966)Termination phase: Saturation
% 4.26/0.96  
% 4.26/0.96  % (9966)Memory used [KB]: 8571
% 4.26/0.96  % (9966)Time elapsed: 0.500 s
% 4.26/0.96  % (9966)------------------------------
% 4.26/0.96  % (9966)------------------------------
% 4.26/0.98  % (10041)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.26/1.00  % (9970)Time limit reached!
% 4.26/1.00  % (9970)------------------------------
% 4.26/1.00  % (9970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/1.02  % (9970)Termination reason: Time limit
% 4.26/1.02  % (9970)Termination phase: Saturation
% 4.26/1.02  
% 4.26/1.02  % (9970)Memory used [KB]: 15223
% 4.26/1.02  % (9970)Time elapsed: 0.600 s
% 4.26/1.02  % (9970)------------------------------
% 4.26/1.02  % (9970)------------------------------
% 4.66/1.03  % (9982)Time limit reached!
% 4.66/1.03  % (9982)------------------------------
% 4.66/1.03  % (9982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.03  % (9982)Termination reason: Time limit
% 4.66/1.03  % (9982)Termination phase: Saturation
% 4.66/1.03  
% 4.66/1.03  % (9982)Memory used [KB]: 7419
% 4.66/1.03  % (9982)Time elapsed: 0.600 s
% 4.66/1.03  % (9982)------------------------------
% 4.66/1.03  % (9982)------------------------------
% 4.66/1.03  % (10066)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.66/1.06  % (9998)Time limit reached!
% 4.66/1.06  % (9998)------------------------------
% 4.66/1.06  % (9998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.06  % (9998)Termination reason: Time limit
% 4.66/1.06  % (9998)Termination phase: Saturation
% 4.66/1.06  
% 4.66/1.06  % (9998)Memory used [KB]: 7803
% 4.66/1.06  % (9998)Time elapsed: 0.400 s
% 4.66/1.06  % (9998)------------------------------
% 4.66/1.06  % (9998)------------------------------
% 4.66/1.06  % (10108)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.66/1.06  % (9961)Time limit reached!
% 4.66/1.06  % (9961)------------------------------
% 4.66/1.06  % (9961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.06  % (9961)Termination reason: Time limit
% 4.66/1.06  
% 4.66/1.06  % (9961)Memory used [KB]: 11257
% 4.66/1.06  % (9961)Time elapsed: 0.613 s
% 4.66/1.06  % (9961)------------------------------
% 4.66/1.06  % (9961)------------------------------
% 4.66/1.07  % (9999)Time limit reached!
% 4.66/1.07  % (9999)------------------------------
% 4.66/1.07  % (9999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.07  % (9999)Termination reason: Time limit
% 4.66/1.07  % (9999)Termination phase: Saturation
% 4.66/1.07  
% 4.66/1.07  % (9999)Memory used [KB]: 13176
% 4.66/1.07  % (9999)Time elapsed: 0.400 s
% 4.66/1.07  % (9999)------------------------------
% 4.66/1.07  % (9999)------------------------------
% 5.54/1.08  % (10093)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.54/1.12  % (10143)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.54/1.13  % (10147)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.39/1.19  % (10157)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.39/1.19  % (10159)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.39/1.21  % (10163)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.78/1.24  % (9975)Time limit reached!
% 6.78/1.24  % (9975)------------------------------
% 6.78/1.24  % (9975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.78/1.24  % (9975)Termination reason: Time limit
% 6.78/1.24  
% 6.78/1.24  % (9975)Memory used [KB]: 3582
% 6.78/1.24  % (9975)Time elapsed: 0.822 s
% 6.78/1.24  % (9975)------------------------------
% 6.78/1.24  % (9975)------------------------------
% 7.37/1.35  % (10189)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 7.75/1.44  % (9956)Time limit reached!
% 7.75/1.44  % (9956)------------------------------
% 7.75/1.44  % (9956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.75/1.44  % (9956)Termination reason: Time limit
% 7.75/1.44  
% 7.75/1.44  % (9956)Memory used [KB]: 18166
% 7.75/1.44  % (9956)Time elapsed: 1.025 s
% 7.75/1.44  % (9956)------------------------------
% 7.75/1.44  % (9956)------------------------------
% 9.10/1.59  % (10238)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.10/1.61  % (10159)Time limit reached!
% 9.10/1.61  % (10159)------------------------------
% 9.10/1.61  % (10159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.10/1.61  % (10159)Termination reason: Time limit
% 9.10/1.61  
% 9.10/1.61  % (10159)Memory used [KB]: 2302
% 9.10/1.61  % (10159)Time elapsed: 0.532 s
% 9.10/1.61  % (10159)------------------------------
% 9.10/1.61  % (10159)------------------------------
% 9.10/1.61  % (9980)Time limit reached!
% 9.10/1.61  % (9980)------------------------------
% 9.10/1.61  % (9980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.10/1.61  % (9980)Termination reason: Time limit
% 9.10/1.61  % (9980)Termination phase: Saturation
% 9.10/1.61  
% 9.10/1.61  % (9980)Memory used [KB]: 14456
% 9.10/1.61  % (9980)Time elapsed: 1.200 s
% 9.10/1.61  % (9980)------------------------------
% 9.10/1.61  % (9980)------------------------------
% 10.31/1.70  % (10239)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.31/1.73  % (9978)Time limit reached!
% 10.31/1.73  % (9978)------------------------------
% 10.31/1.73  % (9978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.31/1.73  % (9978)Termination reason: Time limit
% 10.31/1.73  
% 10.31/1.73  % (9978)Memory used [KB]: 21748
% 10.31/1.73  % (9978)Time elapsed: 1.322 s
% 10.31/1.73  % (9978)------------------------------
% 10.31/1.73  % (9978)------------------------------
% 10.31/1.73  % (9981)Refutation found. Thanks to Tanya!
% 10.31/1.73  % SZS status Theorem for theBenchmark
% 10.31/1.74  % SZS output start Proof for theBenchmark
% 10.31/1.74  fof(f19019,plain,(
% 10.31/1.74    $false),
% 10.31/1.74    inference(avatar_sat_refutation,[],[f245,f246,f443,f464,f2339,f2343,f2385,f2391,f2515,f5064,f5080,f5926,f12653,f12809,f12811,f12831,f12889,f12900,f12909,f13003,f13004,f13012,f13013,f13014,f13015,f13113,f13177,f14208,f14282,f17740,f18448,f18802,f18965,f18975,f19009])).
% 10.31/1.74  fof(f19009,plain,(
% 10.31/1.74    spl16_219 | ~spl16_2 | ~spl16_34 | ~spl16_117),
% 10.31/1.74    inference(avatar_split_clause,[],[f6614,f5333,f2185,f242,f12717])).
% 10.31/1.74  fof(f12717,plain,(
% 10.31/1.74    spl16_219 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_219])])).
% 10.31/1.74  fof(f242,plain,(
% 10.31/1.74    spl16_2 <=> v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 10.31/1.74  fof(f2185,plain,(
% 10.31/1.74    spl16_34 <=> ! [X5] : ~r2_hidden(X5,sK8)),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).
% 10.31/1.74  fof(f5333,plain,(
% 10.31/1.74    spl16_117 <=> u1_struct_0(sK7) = sK8),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_117])])).
% 10.31/1.74  fof(f6614,plain,(
% 10.31/1.74    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | (~spl16_2 | ~spl16_34 | ~spl16_117)),
% 10.31/1.74    inference(backward_demodulation,[],[f6458,f6554])).
% 10.31/1.74  fof(f6554,plain,(
% 10.31/1.74    k1_xboole_0 = u1_struct_0(sK7) | (~spl16_34 | ~spl16_117)),
% 10.31/1.74    inference(forward_demodulation,[],[f5335,f4771])).
% 10.31/1.74  fof(f4771,plain,(
% 10.31/1.74    k1_xboole_0 = sK8 | ~spl16_34),
% 10.31/1.74    inference(resolution,[],[f2186,f173])).
% 10.31/1.74  fof(f173,plain,(
% 10.31/1.74    ( ! [X0] : (r2_hidden(sK12(X0),X0) | k1_xboole_0 = X0) )),
% 10.31/1.74    inference(cnf_transformation,[],[f109])).
% 10.31/1.74  fof(f109,plain,(
% 10.31/1.74    ! [X0] : ((sP3(sK12(X0),X0) & r2_hidden(sK12(X0),X0)) | k1_xboole_0 = X0)),
% 10.31/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f81,f108])).
% 10.31/1.74  fof(f108,plain,(
% 10.31/1.74    ! [X0] : (? [X1] : (sP3(X1,X0) & r2_hidden(X1,X0)) => (sP3(sK12(X0),X0) & r2_hidden(sK12(X0),X0)))),
% 10.31/1.74    introduced(choice_axiom,[])).
% 10.31/1.74  fof(f81,plain,(
% 10.31/1.74    ! [X0] : (? [X1] : (sP3(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 10.31/1.74    inference(definition_folding,[],[f55,f80])).
% 10.31/1.74  fof(f80,plain,(
% 10.31/1.74    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP3(X1,X0))),
% 10.31/1.74    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 10.31/1.74  fof(f55,plain,(
% 10.31/1.74    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 10.31/1.74    inference(ennf_transformation,[],[f22])).
% 10.31/1.74  fof(f22,axiom,(
% 10.31/1.74    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 10.31/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 10.31/1.74  fof(f2186,plain,(
% 10.31/1.74    ( ! [X5] : (~r2_hidden(X5,sK8)) ) | ~spl16_34),
% 10.31/1.74    inference(avatar_component_clause,[],[f2185])).
% 10.31/1.74  fof(f5335,plain,(
% 10.31/1.74    u1_struct_0(sK7) = sK8 | ~spl16_117),
% 10.31/1.74    inference(avatar_component_clause,[],[f5333])).
% 10.31/1.74  fof(f6458,plain,(
% 10.31/1.74    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | (~spl16_2 | ~spl16_34)),
% 10.31/1.74    inference(backward_demodulation,[],[f255,f4771])).
% 10.31/1.74  fof(f255,plain,(
% 10.31/1.74    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~spl16_2),
% 10.31/1.74    inference(forward_demodulation,[],[f243,f140])).
% 10.31/1.74  fof(f140,plain,(
% 10.31/1.74    sK8 = sK9),
% 10.31/1.74    inference(cnf_transformation,[],[f92])).
% 10.31/1.74  fof(f92,plain,(
% 10.31/1.74    ((((~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)) & (v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)) & sK8 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_pre_topc(sK7) & v2_pre_topc(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 10.31/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f87,f91,f90,f89,f88])).
% 10.31/1.74  fof(f88,plain,(
% 10.31/1.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK6,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK6,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 10.31/1.74    introduced(choice_axiom,[])).
% 10.31/1.74  fof(f89,plain,(
% 10.31/1.74    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK6,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK6,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(X2,sK6,sK7)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(X2,sK6,sK7)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_pre_topc(sK7) & v2_pre_topc(sK7))),
% 10.31/1.74    introduced(choice_axiom,[])).
% 10.31/1.74  fof(f90,plain,(
% 10.31/1.74    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(X2,sK6,sK7)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(X2,sK6,sK7)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)) & sK8 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8))),
% 10.31/1.74    introduced(choice_axiom,[])).
% 10.31/1.74  fof(f91,plain,(
% 10.31/1.74    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)) & sK8 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)) & (v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)) & sK8 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(sK9))),
% 10.31/1.74    introduced(choice_axiom,[])).
% 10.31/1.74  fof(f87,plain,(
% 10.31/1.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 10.31/1.74    inference(flattening,[],[f86])).
% 10.31/1.74  fof(f86,plain,(
% 10.31/1.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 10.31/1.74    inference(nnf_transformation,[],[f38])).
% 10.31/1.74  fof(f38,plain,(
% 10.31/1.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 10.31/1.74    inference(flattening,[],[f37])).
% 10.31/1.74  fof(f37,plain,(
% 10.31/1.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 10.31/1.74    inference(ennf_transformation,[],[f36])).
% 10.31/1.74  fof(f36,negated_conjecture,(
% 10.31/1.74    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 10.31/1.74    inference(negated_conjecture,[],[f35])).
% 10.31/1.74  fof(f35,conjecture,(
% 10.31/1.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 10.31/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 10.31/1.74  fof(f243,plain,(
% 10.31/1.74    v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~spl16_2),
% 10.31/1.74    inference(avatar_component_clause,[],[f242])).
% 10.31/1.74  fof(f18975,plain,(
% 10.31/1.74    ~spl16_220 | ~spl16_34 | spl16_48),
% 10.31/1.74    inference(avatar_split_clause,[],[f12659,f2504,f2185,f12744])).
% 10.31/1.74  fof(f12744,plain,(
% 10.31/1.74    spl16_220 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_220])])).
% 10.31/1.74  fof(f2504,plain,(
% 10.31/1.74    spl16_48 <=> v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).
% 10.31/1.74  fof(f12659,plain,(
% 10.31/1.74    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | (~spl16_34 | spl16_48)),
% 10.31/1.74    inference(forward_demodulation,[],[f2505,f4771])).
% 10.31/1.74  fof(f2505,plain,(
% 10.31/1.74    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | spl16_48),
% 10.31/1.74    inference(avatar_component_clause,[],[f2504])).
% 10.31/1.74  fof(f18965,plain,(
% 10.31/1.74    spl16_117 | ~spl16_4 | ~spl16_116),
% 10.31/1.74    inference(avatar_split_clause,[],[f13426,f5329,f287,f5333])).
% 10.31/1.74  fof(f287,plain,(
% 10.31/1.74    spl16_4 <=> r1_tarski(sK8,u1_struct_0(sK7))),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 10.31/1.74  fof(f5329,plain,(
% 10.31/1.74    spl16_116 <=> r1_tarski(u1_struct_0(sK7),sK8)),
% 10.31/1.74    introduced(avatar_definition,[new_symbols(naming,[spl16_116])])).
% 10.31/1.74  fof(f13426,plain,(
% 10.31/1.74    u1_struct_0(sK7) = sK8 | (~spl16_4 | ~spl16_116)),
% 10.31/1.74    inference(subsumption_resolution,[],[f13417,f289])).
% 10.31/1.74  fof(f289,plain,(
% 10.31/1.74    r1_tarski(sK8,u1_struct_0(sK7)) | ~spl16_4),
% 10.31/1.74    inference(avatar_component_clause,[],[f287])).
% 10.31/1.74  fof(f13417,plain,(
% 10.31/1.74    u1_struct_0(sK7) = sK8 | ~r1_tarski(sK8,u1_struct_0(sK7)) | ~spl16_116),
% 10.31/1.74    inference(resolution,[],[f5330,f191])).
% 10.31/1.74  fof(f191,plain,(
% 10.31/1.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 10.31/1.74    inference(cnf_transformation,[],[f115])).
% 10.31/1.74  fof(f115,plain,(
% 10.31/1.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.31/1.74    inference(flattening,[],[f114])).
% 10.31/1.75  fof(f114,plain,(
% 10.31/1.75    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.31/1.75    inference(nnf_transformation,[],[f5])).
% 10.31/1.75  fof(f5,axiom,(
% 10.31/1.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.31/1.75  fof(f5330,plain,(
% 10.31/1.75    r1_tarski(u1_struct_0(sK7),sK8) | ~spl16_116),
% 10.31/1.75    inference(avatar_component_clause,[],[f5329])).
% 10.31/1.75  fof(f18802,plain,(
% 10.31/1.75    ~spl16_232 | spl16_3 | spl16_104 | ~spl16_227),
% 10.31/1.75    inference(avatar_split_clause,[],[f18801,f12968,f5068,f283,f12996])).
% 10.31/1.75  fof(f12996,plain,(
% 10.31/1.75    spl16_232 <=> v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_232])])).
% 10.31/1.75  fof(f283,plain,(
% 10.31/1.75    spl16_3 <=> v1_xboole_0(u1_struct_0(sK7))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).
% 10.31/1.75  fof(f5068,plain,(
% 10.31/1.75    spl16_104 <=> v1_partfun1(sK8,u1_struct_0(sK6))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_104])])).
% 10.31/1.75  fof(f12968,plain,(
% 10.31/1.75    spl16_227 <=> v1_funct_1(sK8)),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_227])])).
% 10.31/1.75  fof(f18801,plain,(
% 10.31/1.75    v1_partfun1(sK8,u1_struct_0(sK6)) | v1_xboole_0(u1_struct_0(sK7)) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~spl16_227),
% 10.31/1.75    inference(subsumption_resolution,[],[f13279,f12969])).
% 10.31/1.75  fof(f12969,plain,(
% 10.31/1.75    v1_funct_1(sK8) | ~spl16_227),
% 10.31/1.75    inference(avatar_component_clause,[],[f12968])).
% 10.31/1.75  fof(f13279,plain,(
% 10.31/1.75    ~v1_funct_1(sK8) | v1_partfun1(sK8,u1_struct_0(sK6)) | v1_xboole_0(u1_struct_0(sK7)) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 10.31/1.75    inference(resolution,[],[f269,f1991])).
% 10.31/1.75  fof(f1991,plain,(
% 10.31/1.75    ( ! [X17,X18,X16] : (~r1_tarski(X16,k2_zfmisc_1(X17,X18)) | ~v1_funct_1(X16) | v1_partfun1(X16,X17) | v1_xboole_0(X18) | ~v1_funct_2(X16,X17,X18)) )),
% 10.31/1.75    inference(resolution,[],[f176,f202])).
% 10.31/1.75  fof(f202,plain,(
% 10.31/1.75    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f125])).
% 10.31/1.75  fof(f125,plain,(
% 10.31/1.75    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 10.31/1.75    inference(nnf_transformation,[],[f11])).
% 10.31/1.75  fof(f11,axiom,(
% 10.31/1.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 10.31/1.75  fof(f176,plain,(
% 10.31/1.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f57])).
% 10.31/1.75  fof(f57,plain,(
% 10.31/1.75    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 10.31/1.75    inference(flattening,[],[f56])).
% 10.31/1.75  fof(f56,plain,(
% 10.31/1.75    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 10.31/1.75    inference(ennf_transformation,[],[f23])).
% 10.31/1.75  fof(f23,axiom,(
% 10.31/1.75    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 10.31/1.75  fof(f269,plain,(
% 10.31/1.75    r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))),
% 10.31/1.75    inference(resolution,[],[f201,f136])).
% 10.31/1.75  fof(f136,plain,(
% 10.31/1.75    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f201,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f125])).
% 10.31/1.75  fof(f18448,plain,(
% 10.31/1.75    spl16_43 | ~spl16_143 | ~spl16_227),
% 10.31/1.75    inference(avatar_contradiction_clause,[],[f18447])).
% 10.31/1.75  fof(f18447,plain,(
% 10.31/1.75    $false | (spl16_43 | ~spl16_143 | ~spl16_227)),
% 10.31/1.75    inference(subsumption_resolution,[],[f18446,f859])).
% 10.31/1.75  % (10240)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 10.31/1.75  fof(f859,plain,(
% 10.31/1.75    v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 10.31/1.75    inference(resolution,[],[f215,f259])).
% 10.31/1.75  fof(f259,plain,(
% 10.31/1.75    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))),
% 10.31/1.75    inference(forward_demodulation,[],[f139,f140])).
% 10.31/1.75  fof(f139,plain,(
% 10.31/1.75    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f215,plain,(
% 10.31/1.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f68])).
% 10.31/1.75  fof(f68,plain,(
% 10.31/1.75    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.31/1.75    inference(ennf_transformation,[],[f18])).
% 10.31/1.75  fof(f18,axiom,(
% 10.31/1.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 10.31/1.75  fof(f18446,plain,(
% 10.31/1.75    ~v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | (spl16_43 | ~spl16_143 | ~spl16_227)),
% 10.31/1.75    inference(subsumption_resolution,[],[f18445,f446])).
% 10.31/1.75  fof(f446,plain,(
% 10.31/1.75    v1_relat_1(sK8)),
% 10.31/1.75    inference(resolution,[],[f212,f136])).
% 10.31/1.75  fof(f212,plain,(
% 10.31/1.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f66])).
% 10.31/1.75  fof(f66,plain,(
% 10.31/1.75    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.31/1.75    inference(ennf_transformation,[],[f17])).
% 10.31/1.75  fof(f17,axiom,(
% 10.31/1.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 10.31/1.75  fof(f18445,plain,(
% 10.31/1.75    ~v1_relat_1(sK8) | ~v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | (spl16_43 | ~spl16_143 | ~spl16_227)),
% 10.31/1.75    inference(subsumption_resolution,[],[f18443,f12969])).
% 10.31/1.75  fof(f18443,plain,(
% 10.31/1.75    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | (spl16_43 | ~spl16_143)),
% 10.31/1.75    inference(resolution,[],[f18427,f1271])).
% 10.31/1.75  fof(f1271,plain,(
% 10.31/1.75    ( ! [X0,X1] : (sP4(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 10.31/1.75    inference(duplicate_literal_removal,[],[f1265])).
% 10.31/1.75  fof(f1265,plain,(
% 10.31/1.75    ( ! [X0,X1] : (sP4(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.31/1.75    inference(resolution,[],[f186,f177])).
% 10.31/1.75  fof(f177,plain,(
% 10.31/1.75    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f110])).
% 10.31/1.75  fof(f110,plain,(
% 10.31/1.75    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(nnf_transformation,[],[f58])).
% 10.31/1.75  fof(f58,plain,(
% 10.31/1.75    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(ennf_transformation,[],[f14])).
% 10.31/1.75  fof(f14,axiom,(
% 10.31/1.75    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 10.31/1.75  fof(f186,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP4(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f83])).
% 10.31/1.75  fof(f83,plain,(
% 10.31/1.75    ! [X0,X1] : (sP4(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(definition_folding,[],[f62,f82])).
% 10.31/1.75  fof(f82,plain,(
% 10.31/1.75    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP4(X0,X1))),
% 10.31/1.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 10.31/1.75  fof(f62,plain,(
% 10.31/1.75    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(flattening,[],[f61])).
% 10.31/1.75  fof(f61,plain,(
% 10.31/1.75    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 10.31/1.75    inference(ennf_transformation,[],[f27])).
% 10.31/1.75  fof(f27,axiom,(
% 10.31/1.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 10.31/1.75  fof(f18427,plain,(
% 10.31/1.75    ~sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8) | (spl16_43 | ~spl16_143)),
% 10.31/1.75    inference(resolution,[],[f17700,f185])).
% 10.31/1.75  fof(f185,plain,(
% 10.31/1.75    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP4(X0,X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f112])).
% 10.31/1.75  fof(f112,plain,(
% 10.31/1.75    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP4(X0,X1))),
% 10.31/1.75    inference(nnf_transformation,[],[f82])).
% 10.31/1.75  fof(f17700,plain,(
% 10.31/1.75    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | (spl16_43 | ~spl16_143)),
% 10.31/1.75    inference(forward_demodulation,[],[f2380,f6091])).
% 10.31/1.75  fof(f6091,plain,(
% 10.31/1.75    u1_struct_0(sK6) = k1_relat_1(sK8) | ~spl16_143),
% 10.31/1.75    inference(avatar_component_clause,[],[f6089])).
% 10.31/1.75  fof(f6089,plain,(
% 10.31/1.75    spl16_143 <=> u1_struct_0(sK6) = k1_relat_1(sK8)),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_143])])).
% 10.31/1.75  fof(f2380,plain,(
% 10.31/1.75    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | spl16_43),
% 10.31/1.75    inference(avatar_component_clause,[],[f2378])).
% 10.31/1.75  fof(f2378,plain,(
% 10.31/1.75    spl16_43 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_43])])).
% 10.31/1.75  fof(f17740,plain,(
% 10.31/1.75    ~spl16_3 | spl16_116),
% 10.31/1.75    inference(avatar_split_clause,[],[f5358,f5329,f283])).
% 10.31/1.75  fof(f5358,plain,(
% 10.31/1.75    ~v1_xboole_0(u1_struct_0(sK7)) | spl16_116),
% 10.31/1.75    inference(resolution,[],[f5331,f422])).
% 10.31/1.75  fof(f422,plain,(
% 10.31/1.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 10.31/1.75    inference(resolution,[],[f193,f169])).
% 10.31/1.75  fof(f169,plain,(
% 10.31/1.75    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f105])).
% 10.31/1.75  fof(f105,plain,(
% 10.31/1.75    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK11(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 10.31/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f103,f104])).
% 10.31/1.75  fof(f104,plain,(
% 10.31/1.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK11(X0),X0))),
% 10.31/1.75    introduced(choice_axiom,[])).
% 10.31/1.75  fof(f103,plain,(
% 10.31/1.75    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 10.31/1.75    inference(rectify,[],[f102])).
% 10.31/1.75  fof(f102,plain,(
% 10.31/1.75    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 10.31/1.75    inference(nnf_transformation,[],[f1])).
% 10.31/1.75  fof(f1,axiom,(
% 10.31/1.75    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 10.31/1.75  fof(f193,plain,(
% 10.31/1.75    ( ! [X0,X1] : (r2_hidden(sK13(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f119])).
% 10.31/1.75  fof(f119,plain,(
% 10.31/1.75    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 10.31/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f117,f118])).
% 10.31/1.75  fof(f118,plain,(
% 10.31/1.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0)))),
% 10.31/1.75    introduced(choice_axiom,[])).
% 10.31/1.75  fof(f117,plain,(
% 10.31/1.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 10.31/1.75    inference(rectify,[],[f116])).
% 10.31/1.75  fof(f116,plain,(
% 10.31/1.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 10.31/1.75    inference(nnf_transformation,[],[f65])).
% 10.31/1.75  fof(f65,plain,(
% 10.31/1.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 10.31/1.75    inference(ennf_transformation,[],[f2])).
% 10.31/1.75  fof(f2,axiom,(
% 10.31/1.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 10.31/1.75  fof(f5331,plain,(
% 10.31/1.75    ~r1_tarski(u1_struct_0(sK7),sK8) | spl16_116),
% 10.31/1.75    inference(avatar_component_clause,[],[f5329])).
% 10.31/1.75  fof(f14282,plain,(
% 10.31/1.75    spl16_143 | ~spl16_142),
% 10.31/1.75    inference(avatar_split_clause,[],[f14281,f6085,f6089])).
% 10.31/1.75  fof(f6085,plain,(
% 10.31/1.75    spl16_142 <=> r1_tarski(u1_struct_0(sK6),k1_relat_1(sK8))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_142])])).
% 10.31/1.75  fof(f14281,plain,(
% 10.31/1.75    u1_struct_0(sK6) = k1_relat_1(sK8) | ~spl16_142),
% 10.31/1.75    inference(subsumption_resolution,[],[f14280,f446])).
% 10.31/1.75  fof(f14280,plain,(
% 10.31/1.75    u1_struct_0(sK6) = k1_relat_1(sK8) | ~v1_relat_1(sK8) | ~spl16_142),
% 10.31/1.75    inference(subsumption_resolution,[],[f14268,f818])).
% 10.31/1.75  fof(f818,plain,(
% 10.31/1.75    v4_relat_1(sK8,u1_struct_0(sK6))),
% 10.31/1.75    inference(resolution,[],[f214,f136])).
% 10.31/1.75  fof(f214,plain,(
% 10.31/1.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f68])).
% 10.31/1.75  fof(f14268,plain,(
% 10.31/1.75    u1_struct_0(sK6) = k1_relat_1(sK8) | ~v4_relat_1(sK8,u1_struct_0(sK6)) | ~v1_relat_1(sK8) | ~spl16_142),
% 10.31/1.75    inference(resolution,[],[f6086,f642])).
% 10.31/1.75  fof(f642,plain,(
% 10.31/1.75    ( ! [X4,X3] : (~r1_tarski(X3,k1_relat_1(X4)) | k1_relat_1(X4) = X3 | ~v4_relat_1(X4,X3) | ~v1_relat_1(X4)) )),
% 10.31/1.75    inference(resolution,[],[f191,f179])).
% 10.31/1.75  fof(f179,plain,(
% 10.31/1.75    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f111])).
% 10.31/1.75  fof(f111,plain,(
% 10.31/1.75    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(nnf_transformation,[],[f59])).
% 10.31/1.75  fof(f59,plain,(
% 10.31/1.75    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(ennf_transformation,[],[f13])).
% 10.31/1.75  fof(f13,axiom,(
% 10.31/1.75    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 10.31/1.75  fof(f6086,plain,(
% 10.31/1.75    r1_tarski(u1_struct_0(sK6),k1_relat_1(sK8)) | ~spl16_142),
% 10.31/1.75    inference(avatar_component_clause,[],[f6085])).
% 10.31/1.75  fof(f14208,plain,(
% 10.31/1.75    ~spl16_104 | spl16_142),
% 10.31/1.75    inference(avatar_contradiction_clause,[],[f14207])).
% 10.31/1.75  fof(f14207,plain,(
% 10.31/1.75    $false | (~spl16_104 | spl16_142)),
% 10.31/1.75    inference(subsumption_resolution,[],[f14174,f5873])).
% 10.31/1.75  fof(f5873,plain,(
% 10.31/1.75    v4_relat_1(sK8,k1_relat_1(sK8))),
% 10.31/1.75    inference(resolution,[],[f5857,f228])).
% 10.31/1.75  fof(f228,plain,(
% 10.31/1.75    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.31/1.75    inference(equality_resolution,[],[f190])).
% 10.31/1.75  fof(f190,plain,(
% 10.31/1.75    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.31/1.75    inference(cnf_transformation,[],[f115])).
% 10.31/1.75  fof(f5857,plain,(
% 10.31/1.75    ( ! [X21] : (~r1_tarski(k1_relat_1(sK8),X21) | v4_relat_1(sK8,X21)) )),
% 10.31/1.75    inference(resolution,[],[f1953,f136])).
% 10.31/1.75  fof(f1953,plain,(
% 10.31/1.75    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~r1_tarski(k1_relat_1(X4),X5) | v4_relat_1(X4,X5)) )),
% 10.31/1.75    inference(resolution,[],[f220,f214])).
% 10.31/1.75  fof(f220,plain,(
% 10.31/1.75    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 10.31/1.75    inference(cnf_transformation,[],[f74])).
% 10.31/1.75  fof(f74,plain,(
% 10.31/1.75    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 10.31/1.75    inference(flattening,[],[f73])).
% 10.31/1.75  fof(f73,plain,(
% 10.31/1.75    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 10.31/1.75    inference(ennf_transformation,[],[f20])).
% 10.31/1.75  fof(f20,axiom,(
% 10.31/1.75    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 10.31/1.75  fof(f14174,plain,(
% 10.31/1.75    ~v4_relat_1(sK8,k1_relat_1(sK8)) | (~spl16_104 | spl16_142)),
% 10.31/1.75    inference(resolution,[],[f13351,f6087])).
% 10.31/1.75  fof(f6087,plain,(
% 10.31/1.75    ~r1_tarski(u1_struct_0(sK6),k1_relat_1(sK8)) | spl16_142),
% 10.31/1.75    inference(avatar_component_clause,[],[f6085])).
% 10.31/1.75  fof(f13351,plain,(
% 10.31/1.75    ( ! [X1] : (r1_tarski(u1_struct_0(sK6),X1) | ~v4_relat_1(sK8,X1)) ) | ~spl16_104),
% 10.31/1.75    inference(subsumption_resolution,[],[f13350,f818])).
% 10.31/1.75  fof(f13350,plain,(
% 10.31/1.75    ( ! [X1] : (~v4_relat_1(sK8,X1) | r1_tarski(u1_struct_0(sK6),X1) | ~v4_relat_1(sK8,u1_struct_0(sK6))) ) | ~spl16_104),
% 10.31/1.75    inference(subsumption_resolution,[],[f13239,f446])).
% 10.31/1.75  fof(f13239,plain,(
% 10.31/1.75    ( ! [X1] : (~v4_relat_1(sK8,X1) | ~v1_relat_1(sK8) | r1_tarski(u1_struct_0(sK6),X1) | ~v4_relat_1(sK8,u1_struct_0(sK6))) ) | ~spl16_104),
% 10.31/1.75    inference(resolution,[],[f5070,f1550])).
% 10.31/1.75  fof(f1550,plain,(
% 10.31/1.75    ( ! [X8,X7,X9] : (~v1_partfun1(X7,X8) | ~v4_relat_1(X7,X9) | ~v1_relat_1(X7) | r1_tarski(X8,X9) | ~v4_relat_1(X7,X8)) )),
% 10.31/1.75    inference(duplicate_literal_removal,[],[f1538])).
% 10.31/1.75  fof(f1538,plain,(
% 10.31/1.75    ( ! [X8,X7,X9] : (r1_tarski(X8,X9) | ~v4_relat_1(X7,X9) | ~v1_relat_1(X7) | ~v1_partfun1(X7,X8) | ~v4_relat_1(X7,X8) | ~v1_relat_1(X7)) )),
% 10.31/1.75    inference(superposition,[],[f179,f187])).
% 10.31/1.75  fof(f187,plain,(
% 10.31/1.75    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f113])).
% 10.31/1.75  fof(f113,plain,(
% 10.31/1.75    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(nnf_transformation,[],[f64])).
% 10.31/1.75  fof(f64,plain,(
% 10.31/1.75    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.31/1.75    inference(flattening,[],[f63])).
% 10.31/1.75  fof(f63,plain,(
% 10.31/1.75    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 10.31/1.75    inference(ennf_transformation,[],[f24])).
% 10.31/1.75  fof(f24,axiom,(
% 10.31/1.75    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 10.31/1.75  fof(f5070,plain,(
% 10.31/1.75    v1_partfun1(sK8,u1_struct_0(sK6)) | ~spl16_104),
% 10.31/1.75    inference(avatar_component_clause,[],[f5068])).
% 10.31/1.75  fof(f13177,plain,(
% 10.31/1.75    ~spl16_41 | ~spl16_39 | ~spl16_42 | ~spl16_43 | ~spl16_228 | spl16_229 | ~spl16_44 | ~spl16_227),
% 10.31/1.75    inference(avatar_split_clause,[],[f13176,f12968,f2382,f12976,f12972,f2378,f2374,f2323,f2370])).
% 10.31/1.75  fof(f2370,plain,(
% 10.31/1.75    spl16_41 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).
% 10.31/1.75  fof(f2323,plain,(
% 10.31/1.75    spl16_39 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).
% 10.31/1.75  fof(f2374,plain,(
% 10.31/1.75    spl16_42 <=> v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).
% 10.31/1.75  fof(f12972,plain,(
% 10.31/1.75    spl16_228 <=> v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_228])])).
% 10.31/1.75  fof(f12976,plain,(
% 10.31/1.75    spl16_229 <=> v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_229])])).
% 10.31/1.75  fof(f2382,plain,(
% 10.31/1.75    spl16_44 <=> v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).
% 10.31/1.75  fof(f13176,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~spl16_227),
% 10.31/1.75    inference(subsumption_resolution,[],[f13175,f130])).
% 10.31/1.75  fof(f130,plain,(
% 10.31/1.75    v2_pre_topc(sK6)),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f13175,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(sK6) | ~spl16_227),
% 10.31/1.75    inference(subsumption_resolution,[],[f13174,f131])).
% 10.31/1.75  fof(f131,plain,(
% 10.31/1.75    l1_pre_topc(sK6)),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f13174,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_227),
% 10.31/1.75    inference(subsumption_resolution,[],[f13135,f12969])).
% 10.31/1.75  fof(f13135,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6)),
% 10.31/1.75    inference(resolution,[],[f259,f233])).
% 10.31/1.75  fof(f233,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(duplicate_literal_removal,[],[f224])).
% 10.31/1.75  fof(f224,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(equality_resolution,[],[f167])).
% 10.31/1.75  fof(f167,plain,(
% 10.31/1.75    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f101])).
% 10.31/1.75  fof(f101,plain,(
% 10.31/1.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 10.31/1.75    inference(nnf_transformation,[],[f54])).
% 10.31/1.75  fof(f54,plain,(
% 10.31/1.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 10.31/1.75    inference(flattening,[],[f53])).
% 10.31/1.75  fof(f53,plain,(
% 10.31/1.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 10.31/1.75    inference(ennf_transformation,[],[f33])).
% 10.31/1.75  fof(f33,axiom,(
% 10.31/1.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 10.31/1.75  fof(f13113,plain,(
% 10.31/1.75    ~spl16_229 | spl16_2),
% 10.31/1.75    inference(avatar_split_clause,[],[f13112,f242,f12976])).
% 10.31/1.75  fof(f13112,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | spl16_2),
% 10.31/1.75    inference(forward_demodulation,[],[f244,f140])).
% 10.31/1.75  fof(f244,plain,(
% 10.31/1.75    ~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | spl16_2),
% 10.31/1.75    inference(avatar_component_clause,[],[f242])).
% 10.31/1.75  fof(f13015,plain,(
% 10.31/1.75    spl16_227),
% 10.31/1.75    inference(avatar_split_clause,[],[f134,f12968])).
% 10.31/1.75  fof(f134,plain,(
% 10.31/1.75    v1_funct_1(sK8)),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f13014,plain,(
% 10.31/1.75    spl16_232),
% 10.31/1.75    inference(avatar_split_clause,[],[f135,f12996])).
% 10.31/1.75  fof(f135,plain,(
% 10.31/1.75    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f13013,plain,(
% 10.31/1.75    spl16_233),
% 10.31/1.75    inference(avatar_split_clause,[],[f136,f13000])).
% 10.31/1.75  fof(f13000,plain,(
% 10.31/1.75    spl16_233 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_233])])).
% 10.31/1.75  fof(f13012,plain,(
% 10.31/1.75    spl16_228),
% 10.31/1.75    inference(avatar_split_clause,[],[f256,f12972])).
% 10.31/1.75  fof(f256,plain,(
% 10.31/1.75    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 10.31/1.75    inference(forward_demodulation,[],[f138,f140])).
% 10.31/1.75  fof(f138,plain,(
% 10.31/1.75    v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f13004,plain,(
% 10.31/1.75    ~spl16_232 | ~spl16_233 | ~spl16_227 | ~spl16_42 | spl16_44 | ~spl16_1 | ~spl16_43),
% 10.31/1.75    inference(avatar_split_clause,[],[f12695,f2378,f238,f2382,f2374,f12968,f13000,f12996])).
% 10.31/1.75  fof(f238,plain,(
% 10.31/1.75    spl16_1 <=> v5_pre_topc(sK8,sK6,sK7)),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 10.31/1.75  fof(f12695,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,sK7) | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~spl16_43),
% 10.31/1.75    inference(subsumption_resolution,[],[f12694,f130])).
% 10.31/1.75  fof(f12694,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,sK7) | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK6) | ~spl16_43),
% 10.31/1.75    inference(subsumption_resolution,[],[f12693,f131])).
% 10.31/1.75  fof(f12693,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,sK7) | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_43),
% 10.31/1.75    inference(subsumption_resolution,[],[f12692,f132])).
% 10.31/1.75  fof(f132,plain,(
% 10.31/1.75    v2_pre_topc(sK7)),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f12692,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,sK7) | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_43),
% 10.31/1.75    inference(subsumption_resolution,[],[f6166,f133])).
% 10.31/1.75  fof(f133,plain,(
% 10.31/1.75    l1_pre_topc(sK7)),
% 10.31/1.75    inference(cnf_transformation,[],[f92])).
% 10.31/1.75  fof(f6166,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,sK7) | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_43),
% 10.31/1.75    inference(resolution,[],[f2379,f235])).
% 10.31/1.75  fof(f235,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(duplicate_literal_removal,[],[f222])).
% 10.31/1.75  fof(f222,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(equality_resolution,[],[f165])).
% 10.31/1.75  fof(f165,plain,(
% 10.31/1.75    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f100])).
% 10.31/1.75  fof(f100,plain,(
% 10.31/1.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 10.31/1.75    inference(nnf_transformation,[],[f52])).
% 10.31/1.75  fof(f52,plain,(
% 10.31/1.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 10.31/1.75    inference(flattening,[],[f51])).
% 10.31/1.75  fof(f51,plain,(
% 10.31/1.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 10.31/1.75    inference(ennf_transformation,[],[f34])).
% 10.31/1.75  fof(f34,axiom,(
% 10.31/1.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 10.31/1.75  fof(f2379,plain,(
% 10.31/1.75    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~spl16_43),
% 10.31/1.75    inference(avatar_component_clause,[],[f2378])).
% 10.31/1.75  fof(f13003,plain,(
% 10.31/1.75    ~spl16_232 | ~spl16_233 | ~spl16_227 | ~spl16_42 | spl16_1 | ~spl16_43 | ~spl16_44),
% 10.31/1.75    inference(avatar_split_clause,[],[f12702,f2382,f2378,f238,f2374,f12968,f13000,f12996])).
% 10.31/1.75  fof(f12702,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,sK7) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_43 | ~spl16_44)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12701,f130])).
% 10.31/1.75  fof(f12701,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,sK7) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK6) | (~spl16_43 | ~spl16_44)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12700,f131])).
% 10.31/1.75  fof(f12700,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,sK7) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_43 | ~spl16_44)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12699,f132])).
% 10.31/1.75  fof(f12699,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,sK7) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_43 | ~spl16_44)),
% 10.31/1.75    inference(subsumption_resolution,[],[f6180,f133])).
% 10.31/1.75  fof(f6180,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,sK7) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_43 | ~spl16_44)),
% 10.31/1.75    inference(subsumption_resolution,[],[f6165,f2384])).
% 10.31/1.75  fof(f2384,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~spl16_44),
% 10.31/1.75    inference(avatar_component_clause,[],[f2382])).
% 10.31/1.75  fof(f6165,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_43),
% 10.31/1.75    inference(resolution,[],[f2379,f236])).
% 10.31/1.75  fof(f236,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(duplicate_literal_removal,[],[f221])).
% 10.31/1.75  fof(f221,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(equality_resolution,[],[f166])).
% 10.31/1.75  fof(f166,plain,(
% 10.31/1.75    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f100])).
% 10.31/1.75  fof(f12909,plain,(
% 10.31/1.75    spl16_221 | ~spl16_34 | ~spl16_117),
% 10.31/1.75    inference(avatar_split_clause,[],[f6615,f5333,f2185,f12842])).
% 10.31/1.75  fof(f12842,plain,(
% 10.31/1.75    spl16_221 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_221])])).
% 10.31/1.75  fof(f6615,plain,(
% 10.31/1.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | (~spl16_34 | ~spl16_117)),
% 10.31/1.75    inference(backward_demodulation,[],[f6459,f6554])).
% 10.31/1.75  fof(f6459,plain,(
% 10.31/1.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~spl16_34),
% 10.31/1.75    inference(backward_demodulation,[],[f256,f4771])).
% 10.31/1.75  fof(f12900,plain,(
% 10.31/1.75    ~spl16_219 | spl16_220 | ~spl16_221 | ~spl16_22 | ~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117),
% 10.31/1.75    inference(avatar_split_clause,[],[f12899,f5333,f2492,f2319,f2185,f405,f401,f12842,f12744,f12717])).
% 10.31/1.75  fof(f401,plain,(
% 10.31/1.75    spl16_22 <=> v1_relat_1(k1_xboole_0)),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).
% 10.31/1.75  fof(f405,plain,(
% 10.31/1.75    spl16_23 <=> v1_funct_1(k1_xboole_0)),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).
% 10.31/1.75  fof(f2319,plain,(
% 10.31/1.75    spl16_38 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).
% 10.31/1.75  fof(f2492,plain,(
% 10.31/1.75    spl16_45 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).
% 10.31/1.75  fof(f12899,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | (~spl16_22 | ~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12898,f1005])).
% 10.31/1.75  fof(f1005,plain,(
% 10.31/1.75    ( ! [X5] : (v1_funct_2(k1_xboole_0,X5,k1_xboole_0)) ) | ~spl16_22),
% 10.31/1.75    inference(superposition,[],[f211,f980])).
% 10.31/1.75  fof(f980,plain,(
% 10.31/1.75    ( ! [X3] : (k1_xboole_0 = sK15(X3,k1_xboole_0)) ) | ~spl16_22),
% 10.31/1.75    inference(subsumption_resolution,[],[f974,f845])).
% 10.31/1.75  fof(f845,plain,(
% 10.31/1.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl16_22),
% 10.31/1.75    inference(subsumption_resolution,[],[f556,f833])).
% 10.31/1.75  fof(f833,plain,(
% 10.31/1.75    ( ! [X4] : (v4_relat_1(k1_xboole_0,X4)) )),
% 10.31/1.75    inference(resolution,[],[f826,f702])).
% 10.31/1.75  fof(f702,plain,(
% 10.31/1.75    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 10.31/1.75    inference(subsumption_resolution,[],[f698,f143])).
% 10.31/1.75  fof(f143,plain,(
% 10.31/1.75    v1_xboole_0(k1_xboole_0)),
% 10.31/1.75    inference(cnf_transformation,[],[f3])).
% 10.31/1.75  fof(f3,axiom,(
% 10.31/1.75    v1_xboole_0(k1_xboole_0)),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 10.31/1.75  fof(f698,plain,(
% 10.31/1.75    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 10.31/1.75    inference(superposition,[],[f431,f670])).
% 10.31/1.75  fof(f670,plain,(
% 10.31/1.75    ( ! [X8,X9] : (sK15(X8,X9) = X8 | ~v1_xboole_0(X8)) )),
% 10.31/1.75    inference(subsumption_resolution,[],[f647,f422])).
% 10.31/1.75  fof(f647,plain,(
% 10.31/1.75    ( ! [X8,X9] : (sK15(X8,X9) = X8 | ~r1_tarski(X8,sK15(X8,X9)) | ~v1_xboole_0(X8)) )),
% 10.31/1.75    inference(resolution,[],[f191,f499])).
% 10.31/1.75  fof(f499,plain,(
% 10.31/1.75    ( ! [X2,X1] : (r1_tarski(sK15(X1,X2),X1) | ~v1_xboole_0(X1)) )),
% 10.31/1.75    inference(superposition,[],[f427,f254])).
% 10.31/1.75  fof(f254,plain,(
% 10.31/1.75    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 10.31/1.75    inference(superposition,[],[f232,f155])).
% 10.31/1.75  fof(f155,plain,(
% 10.31/1.75    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f42])).
% 10.31/1.75  fof(f42,plain,(
% 10.31/1.75    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 10.31/1.75    inference(ennf_transformation,[],[f4])).
% 10.31/1.75  fof(f4,axiom,(
% 10.31/1.75    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 10.31/1.75  fof(f232,plain,(
% 10.31/1.75    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 10.31/1.75    inference(equality_resolution,[],[f204])).
% 10.31/1.75  fof(f204,plain,(
% 10.31/1.75    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 10.31/1.75    inference(cnf_transformation,[],[f127])).
% 10.31/1.75  fof(f127,plain,(
% 10.31/1.75    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 10.31/1.75    inference(flattening,[],[f126])).
% 10.31/1.75  fof(f126,plain,(
% 10.31/1.75    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 10.31/1.75    inference(nnf_transformation,[],[f8])).
% 10.31/1.75  fof(f8,axiom,(
% 10.31/1.75    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 10.31/1.75  fof(f427,plain,(
% 10.31/1.75    ( ! [X2,X3] : (r1_tarski(sK15(X2,X3),k2_zfmisc_1(X2,X3))) )),
% 10.31/1.75    inference(resolution,[],[f206,f201])).
% 10.31/1.75  fof(f206,plain,(
% 10.31/1.75    ( ! [X0,X1] : (m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.31/1.75    inference(cnf_transformation,[],[f129])).
% 10.31/1.75  fof(f129,plain,(
% 10.31/1.75    ! [X0,X1] : (v1_funct_2(sK15(X0,X1),X0,X1) & v1_funct_1(sK15(X0,X1)) & v5_relat_1(sK15(X0,X1),X1) & v4_relat_1(sK15(X0,X1),X0) & v1_relat_1(sK15(X0,X1)) & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.31/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f25,f128])).
% 10.31/1.75  fof(f128,plain,(
% 10.31/1.75    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK15(X0,X1),X0,X1) & v1_funct_1(sK15(X0,X1)) & v5_relat_1(sK15(X0,X1),X1) & v4_relat_1(sK15(X0,X1),X0) & v1_relat_1(sK15(X0,X1)) & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 10.31/1.75    introduced(choice_axiom,[])).
% 10.31/1.75  fof(f25,axiom,(
% 10.31/1.75    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 10.31/1.75  fof(f431,plain,(
% 10.31/1.75    ( ! [X5] : (m1_subset_1(sK15(k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0))) )),
% 10.31/1.75    inference(superposition,[],[f206,f232])).
% 10.31/1.75  fof(f826,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 10.31/1.75    inference(superposition,[],[f214,f231])).
% 10.31/1.75  fof(f231,plain,(
% 10.31/1.75    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 10.31/1.75    inference(equality_resolution,[],[f205])).
% 10.31/1.75  fof(f205,plain,(
% 10.31/1.75    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 10.31/1.75    inference(cnf_transformation,[],[f127])).
% 10.31/1.75  fof(f556,plain,(
% 10.31/1.75    ( ! [X0] : (~v4_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl16_22),
% 10.31/1.75    inference(subsumption_resolution,[],[f554,f402])).
% 10.31/1.75  fof(f402,plain,(
% 10.31/1.75    v1_relat_1(k1_xboole_0) | ~spl16_22),
% 10.31/1.75    inference(avatar_component_clause,[],[f401])).
% 10.31/1.75  fof(f554,plain,(
% 10.31/1.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 10.31/1.75    inference(superposition,[],[f179,f144])).
% 10.31/1.75  fof(f144,plain,(
% 10.31/1.75    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 10.31/1.75    inference(cnf_transformation,[],[f16])).
% 10.31/1.75  fof(f16,axiom,(
% 10.31/1.75    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 10.31/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 10.31/1.75  fof(f974,plain,(
% 10.31/1.75    ( ! [X3] : (k1_xboole_0 = sK15(X3,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK15(X3,k1_xboole_0))) )),
% 10.31/1.75    inference(resolution,[],[f459,f191])).
% 10.31/1.75  fof(f459,plain,(
% 10.31/1.75    ( ! [X1] : (r1_tarski(sK15(X1,k1_xboole_0),k1_xboole_0)) )),
% 10.31/1.75    inference(resolution,[],[f428,f201])).
% 10.31/1.75  fof(f428,plain,(
% 10.31/1.75    ( ! [X0] : (m1_subset_1(sK15(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 10.31/1.75    inference(superposition,[],[f206,f231])).
% 10.31/1.75  fof(f211,plain,(
% 10.31/1.75    ( ! [X0,X1] : (v1_funct_2(sK15(X0,X1),X0,X1)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f129])).
% 10.31/1.75  fof(f12898,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12897,f4771])).
% 10.31/1.75  fof(f12897,plain,(
% 10.31/1.75    ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12896,f6554])).
% 10.31/1.75  fof(f12896,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12895,f702])).
% 10.31/1.75  fof(f12895,plain,(
% 10.31/1.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12894,f4771])).
% 10.31/1.75  fof(f12894,plain,(
% 10.31/1.75    ~m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12893,f231])).
% 10.31/1.75  fof(f12893,plain,(
% 10.31/1.75    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12892,f6554])).
% 10.31/1.75  fof(f12892,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12891,f406])).
% 10.31/1.75  fof(f406,plain,(
% 10.31/1.75    v1_funct_1(k1_xboole_0) | ~spl16_23),
% 10.31/1.75    inference(avatar_component_clause,[],[f405])).
% 10.31/1.75  fof(f12891,plain,(
% 10.31/1.75    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12890,f4771])).
% 10.31/1.75  fof(f12890,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12729,f4771])).
% 10.31/1.75  fof(f12729,plain,(
% 10.31/1.75    ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12728,f6554])).
% 10.31/1.75  fof(f12728,plain,(
% 10.31/1.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12727,f4771])).
% 10.31/1.75  fof(f12727,plain,(
% 10.31/1.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12726,f4771])).
% 10.31/1.75  fof(f12726,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12725,f6554])).
% 10.31/1.75  fof(f12725,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_38 | ~spl16_45)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12724,f2493])).
% 10.31/1.75  fof(f2493,plain,(
% 10.31/1.75    v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_45),
% 10.31/1.75    inference(avatar_component_clause,[],[f2492])).
% 10.31/1.75  fof(f12724,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_38),
% 10.31/1.75    inference(subsumption_resolution,[],[f12723,f2320])).
% 10.31/1.75  fof(f2320,plain,(
% 10.31/1.75    l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_38),
% 10.31/1.75    inference(avatar_component_clause,[],[f2319])).
% 10.31/1.75  fof(f12723,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    inference(subsumption_resolution,[],[f12722,f132])).
% 10.31/1.75  fof(f12722,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~v2_pre_topc(sK7) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    inference(subsumption_resolution,[],[f2478,f133])).
% 10.31/1.75  fof(f2478,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    inference(resolution,[],[f236,f259])).
% 10.31/1.75  fof(f12889,plain,(
% 10.31/1.75    ~spl16_220 | spl16_219 | ~spl16_221 | ~spl16_22 | ~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117),
% 10.31/1.75    inference(avatar_split_clause,[],[f12888,f5333,f2492,f2319,f2185,f405,f401,f12842,f12717,f12744])).
% 10.31/1.75  fof(f12888,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | (~spl16_22 | ~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12887,f1005])).
% 10.31/1.75  fof(f12887,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12886,f4771])).
% 10.31/1.75  fof(f12886,plain,(
% 10.31/1.75    ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12885,f6554])).
% 10.31/1.75  fof(f12885,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12884,f702])).
% 10.31/1.75  fof(f12884,plain,(
% 10.31/1.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12883,f4771])).
% 10.31/1.75  fof(f12883,plain,(
% 10.31/1.75    ~m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12882,f231])).
% 10.31/1.75  fof(f12882,plain,(
% 10.31/1.75    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12881,f6554])).
% 10.31/1.75  fof(f12881,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_23 | ~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12880,f406])).
% 10.31/1.75  fof(f12880,plain,(
% 10.31/1.75    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12879,f4771])).
% 10.31/1.75  fof(f12879,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12755,f4771])).
% 10.31/1.75  fof(f12755,plain,(
% 10.31/1.75    ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12754,f6554])).
% 10.31/1.75  fof(f12754,plain,(
% 10.31/1.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12753,f4771])).
% 10.31/1.75  fof(f12753,plain,(
% 10.31/1.75    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12752,f6554])).
% 10.31/1.75  fof(f12752,plain,(
% 10.31/1.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_38 | ~spl16_45)),
% 10.31/1.75    inference(forward_demodulation,[],[f12751,f4771])).
% 10.31/1.75  fof(f12751,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | (~spl16_38 | ~spl16_45)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12750,f2493])).
% 10.31/1.75  fof(f12750,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_38),
% 10.31/1.75    inference(subsumption_resolution,[],[f12749,f2320])).
% 10.31/1.75  fof(f12749,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    inference(subsumption_resolution,[],[f12748,f132])).
% 10.31/1.75  fof(f12748,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~v2_pre_topc(sK7) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    inference(subsumption_resolution,[],[f2426,f133])).
% 10.31/1.75  fof(f2426,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 10.31/1.75    inference(resolution,[],[f235,f259])).
% 10.31/1.75  fof(f12831,plain,(
% 10.31/1.75    ~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220),
% 10.31/1.75    inference(avatar_contradiction_clause,[],[f12830])).
% 10.31/1.75  fof(f12830,plain,(
% 10.31/1.75    $false | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12829,f1005])).
% 10.31/1.75  fof(f12829,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK6),k1_xboole_0) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12828,f980])).
% 10.31/1.75  fof(f12828,plain,(
% 10.31/1.75    ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),u1_struct_0(sK6),k1_xboole_0) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12827,f6554])).
% 10.31/1.75  fof(f12827,plain,(
% 10.31/1.75    ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12826,f702])).
% 10.31/1.75  fof(f12826,plain,(
% 10.31/1.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12825,f980])).
% 10.31/1.75  fof(f12825,plain,(
% 10.31/1.75    ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12824,f231])).
% 10.31/1.75  fof(f12824,plain,(
% 10.31/1.75    ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12823,f6554])).
% 10.31/1.75  fof(f12823,plain,(
% 10.31/1.75    ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12822,f143])).
% 10.31/1.75  fof(f12822,plain,(
% 10.31/1.75    ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_22 | ~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12821,f980])).
% 10.31/1.75  fof(f12821,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_117 | ~spl16_217 | spl16_220)),
% 10.31/1.75    inference(forward_demodulation,[],[f12820,f6554])).
% 10.31/1.75  fof(f12820,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_217 | spl16_220)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12819,f12813])).
% 10.31/1.75  fof(f12813,plain,(
% 10.31/1.75    ( ! [X0] : (v5_pre_topc(X0,sK6,sK7) | ~v1_xboole_0(X0)) ) | ~spl16_217),
% 10.31/1.75    inference(superposition,[],[f12688,f155])).
% 10.31/1.75  fof(f12688,plain,(
% 10.31/1.75    v5_pre_topc(k1_xboole_0,sK6,sK7) | ~spl16_217),
% 10.31/1.75    inference(avatar_component_clause,[],[f12687])).
% 10.31/1.75  fof(f12687,plain,(
% 10.31/1.75    spl16_217 <=> v5_pre_topc(k1_xboole_0,sK6,sK7)),
% 10.31/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_217])])).
% 10.31/1.75  fof(f12819,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | spl16_220),
% 10.31/1.75    inference(subsumption_resolution,[],[f12818,f130])).
% 10.31/1.75  fof(f12818,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK6) | spl16_220),
% 10.31/1.75    inference(subsumption_resolution,[],[f12817,f131])).
% 10.31/1.75  fof(f12817,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | spl16_220),
% 10.31/1.75    inference(subsumption_resolution,[],[f12816,f132])).
% 10.31/1.75  fof(f12816,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | spl16_220),
% 10.31/1.75    inference(subsumption_resolution,[],[f12815,f133])).
% 10.31/1.75  fof(f12815,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | spl16_220),
% 10.31/1.75    inference(resolution,[],[f12814,f2351])).
% 10.31/1.75  fof(f2351,plain,(
% 10.31/1.75    ( ! [X0,X1] : (v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(subsumption_resolution,[],[f2350,f210])).
% 10.31/1.75  fof(f210,plain,(
% 10.31/1.75    ( ! [X0,X1] : (v1_funct_1(sK15(X0,X1))) )),
% 10.31/1.75    inference(cnf_transformation,[],[f129])).
% 10.31/1.75  fof(f2350,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(subsumption_resolution,[],[f2345,f211])).
% 10.31/1.75  fof(f2345,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(resolution,[],[f233,f206])).
% 10.31/1.75  fof(f12814,plain,(
% 10.31/1.75    ( ! [X0] : (~v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_xboole_0(X0)) ) | spl16_220),
% 10.31/1.75    inference(superposition,[],[f12745,f155])).
% 10.31/1.75  fof(f12745,plain,(
% 10.31/1.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | spl16_220),
% 10.31/1.75    inference(avatar_component_clause,[],[f12744])).
% 10.31/1.75  fof(f12811,plain,(
% 10.31/1.75    spl16_217 | ~spl16_1 | ~spl16_34),
% 10.31/1.75    inference(avatar_split_clause,[],[f12810,f2185,f238,f12687])).
% 10.31/1.75  fof(f12810,plain,(
% 10.31/1.75    v5_pre_topc(k1_xboole_0,sK6,sK7) | (~spl16_1 | ~spl16_34)),
% 10.31/1.75    inference(forward_demodulation,[],[f239,f4771])).
% 10.31/1.75  fof(f239,plain,(
% 10.31/1.75    v5_pre_topc(sK8,sK6,sK7) | ~spl16_1),
% 10.31/1.75    inference(avatar_component_clause,[],[f238])).
% 10.31/1.75  fof(f12809,plain,(
% 10.31/1.75    ~spl16_219 | spl16_2 | ~spl16_34 | ~spl16_117),
% 10.31/1.75    inference(avatar_split_clause,[],[f12808,f5333,f2185,f242,f12717])).
% 10.31/1.75  fof(f12808,plain,(
% 10.31/1.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | (spl16_2 | ~spl16_34 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12807,f6456])).
% 10.31/1.75  fof(f6456,plain,(
% 10.31/1.75    k1_xboole_0 = sK9 | ~spl16_34),
% 10.31/1.75    inference(backward_demodulation,[],[f140,f4771])).
% 10.31/1.75  fof(f12807,plain,(
% 10.31/1.75    ~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) | (spl16_2 | ~spl16_34 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f244,f6554])).
% 10.31/1.75  fof(f12653,plain,(
% 10.31/1.75    spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117),
% 10.31/1.75    inference(avatar_contradiction_clause,[],[f12652])).
% 10.31/1.75  fof(f12652,plain,(
% 10.31/1.75    $false | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12651,f1005])).
% 10.31/1.75  fof(f12651,plain,(
% 10.31/1.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK6),k1_xboole_0) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12650,f980])).
% 10.31/1.75  fof(f12650,plain,(
% 10.31/1.75    ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),u1_struct_0(sK6),k1_xboole_0) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12649,f6554])).
% 10.31/1.75  fof(f12649,plain,(
% 10.31/1.75    ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12648,f702])).
% 10.31/1.75  fof(f12648,plain,(
% 10.31/1.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12647,f980])).
% 10.31/1.75  fof(f12647,plain,(
% 10.31/1.75    ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12646,f231])).
% 10.31/1.75  fof(f12646,plain,(
% 10.31/1.75    ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12645,f6554])).
% 10.31/1.75  fof(f12645,plain,(
% 10.31/1.75    ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12644,f143])).
% 10.31/1.75  fof(f12644,plain,(
% 10.31/1.75    ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_22 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12643,f980])).
% 10.31/1.75  fof(f12643,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_34 | ~spl16_48 | ~spl16_117)),
% 10.31/1.75    inference(forward_demodulation,[],[f12642,f6554])).
% 10.31/1.75  fof(f12642,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (spl16_1 | ~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12641,f6542])).
% 10.31/1.75  fof(f6542,plain,(
% 10.31/1.75    ( ! [X0] : (~v5_pre_topc(X0,sK6,sK7) | ~v1_xboole_0(X0)) ) | (spl16_1 | ~spl16_34)),
% 10.31/1.75    inference(superposition,[],[f6457,f155])).
% 10.31/1.75  fof(f6457,plain,(
% 10.31/1.75    ~v5_pre_topc(k1_xboole_0,sK6,sK7) | (spl16_1 | ~spl16_34)),
% 10.31/1.75    inference(backward_demodulation,[],[f240,f4771])).
% 10.31/1.75  fof(f240,plain,(
% 10.31/1.75    ~v5_pre_topc(sK8,sK6,sK7) | spl16_1),
% 10.31/1.75    inference(avatar_component_clause,[],[f238])).
% 10.31/1.75  fof(f12641,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12640,f130])).
% 10.31/1.75  fof(f12640,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK6) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12639,f131])).
% 10.31/1.75  fof(f12639,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12638,f132])).
% 10.31/1.75  fof(f12638,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(subsumption_resolution,[],[f12637,f133])).
% 10.31/1.75  fof(f12637,plain,(
% 10.31/1.75    ~v1_xboole_0(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),sK6,sK7) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)),u1_struct_0(sK6),u1_struct_0(sK7)) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(resolution,[],[f6976,f2387])).
% 10.31/1.75  fof(f2387,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(subsumption_resolution,[],[f2386,f210])).
% 10.31/1.75  fof(f2386,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1) | ~v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(subsumption_resolution,[],[f2358,f211])).
% 10.31/1.75  fof(f2358,plain,(
% 10.31/1.75    ( ! [X0,X1] : (~v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),X0,X1) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))) | ~m1_subset_1(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK15(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(resolution,[],[f234,f206])).
% 10.31/1.75  fof(f234,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(duplicate_literal_removal,[],[f223])).
% 10.31/1.75  fof(f223,plain,(
% 10.31/1.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(equality_resolution,[],[f168])).
% 10.31/1.75  fof(f168,plain,(
% 10.31/1.75    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.31/1.75    inference(cnf_transformation,[],[f101])).
% 10.31/1.75  fof(f6976,plain,(
% 10.31/1.75    ( ! [X0] : (v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~v1_xboole_0(X0)) ) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(superposition,[],[f6484,f155])).
% 10.31/1.75  fof(f6484,plain,(
% 10.31/1.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | (~spl16_34 | ~spl16_48)),
% 10.31/1.75    inference(backward_demodulation,[],[f2506,f4771])).
% 10.31/1.75  fof(f2506,plain,(
% 10.31/1.75    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) | ~spl16_48),
% 10.31/1.75    inference(avatar_component_clause,[],[f2504])).
% 10.31/1.75  fof(f5926,plain,(
% 10.31/1.75    spl16_42 | ~spl16_104),
% 10.31/1.75    inference(avatar_contradiction_clause,[],[f5925])).
% 10.31/1.75  fof(f5925,plain,(
% 10.31/1.75    $false | (spl16_42 | ~spl16_104)),
% 10.31/1.75    inference(subsumption_resolution,[],[f5924,f859])).
% 10.31/1.75  fof(f5924,plain,(
% 10.31/1.75    ~v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | (spl16_42 | ~spl16_104)),
% 10.31/1.75    inference(subsumption_resolution,[],[f5923,f446])).
% 10.31/1.75  fof(f5923,plain,(
% 10.31/1.75    ~v1_relat_1(sK8) | ~v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | (spl16_42 | ~spl16_104)),
% 10.31/1.75    inference(subsumption_resolution,[],[f5921,f134])).
% 10.31/1.75  fof(f5921,plain,(
% 10.31/1.75    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~v5_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | (spl16_42 | ~spl16_104)),
% 10.31/1.75    inference(resolution,[],[f5712,f1271])).
% 10.31/1.75  fof(f5712,plain,(
% 10.31/1.75    ~sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8) | (spl16_42 | ~spl16_104)),
% 10.31/1.75    inference(subsumption_resolution,[],[f5711,f818])).
% 10.31/1.75  fof(f5711,plain,(
% 10.31/1.75    ~sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8) | ~v4_relat_1(sK8,u1_struct_0(sK6)) | (spl16_42 | ~spl16_104)),
% 10.31/1.75    inference(subsumption_resolution,[],[f5709,f5070])).
% 10.31/1.75  fof(f5709,plain,(
% 10.31/1.75    ~sP4(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK8) | ~v1_partfun1(sK8,u1_struct_0(sK6)) | ~v4_relat_1(sK8,u1_struct_0(sK6)) | spl16_42),
% 10.31/1.75    inference(resolution,[],[f1562,f2376])).
% 10.31/1.75  fof(f2376,plain,(
% 10.31/1.75    ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | spl16_42),
% 10.31/1.75    inference(avatar_component_clause,[],[f2374])).
% 10.31/1.76  fof(f1562,plain,(
% 10.31/1.76    ( ! [X14,X15,X13] : (v1_funct_2(X13,X14,X15) | ~sP4(X15,X13) | ~v1_partfun1(X13,X14) | ~v4_relat_1(X13,X14)) )),
% 10.31/1.76    inference(subsumption_resolution,[],[f1540,f1228])).
% 10.31/1.76  fof(f1228,plain,(
% 10.31/1.76    ( ! [X4,X5] : (~sP4(X4,X5) | v1_relat_1(X5)) )),
% 10.31/1.76    inference(resolution,[],[f185,f212])).
% 10.31/1.76  fof(f1540,plain,(
% 10.31/1.76    ( ! [X14,X15,X13] : (v1_funct_2(X13,X14,X15) | ~sP4(X15,X13) | ~v1_partfun1(X13,X14) | ~v4_relat_1(X13,X14) | ~v1_relat_1(X13)) )),
% 10.31/1.76    inference(superposition,[],[f184,f187])).
% 10.31/1.76  fof(f184,plain,(
% 10.31/1.76    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP4(X0,X1)) )),
% 10.31/1.76    inference(cnf_transformation,[],[f112])).
% 10.31/1.76  fof(f5080,plain,(
% 10.31/1.76    ~spl16_3 | spl16_34),
% 10.31/1.76    inference(avatar_split_clause,[],[f5079,f2185,f283])).
% 10.31/1.76  fof(f5079,plain,(
% 10.31/1.76    ( ! [X1] : (~r2_hidden(X1,sK8) | ~v1_xboole_0(u1_struct_0(sK7))) )),
% 10.31/1.76    inference(subsumption_resolution,[],[f732,f169])).
% 10.31/1.76  fof(f732,plain,(
% 10.31/1.76    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK7)) | ~r2_hidden(X1,sK8) | ~v1_xboole_0(u1_struct_0(sK7))) )),
% 10.31/1.76    inference(superposition,[],[f720,f253])).
% 10.31/1.76  fof(f253,plain,(
% 10.31/1.76    ( ! [X0,X1] : (k2_zfmisc_1(X1,X0) = X0 | ~v1_xboole_0(X0)) )),
% 10.31/1.76    inference(superposition,[],[f231,f155])).
% 10.31/1.76  fof(f720,plain,(
% 10.31/1.76    ( ! [X13] : (r2_hidden(X13,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))) | ~r2_hidden(X13,sK8)) )),
% 10.31/1.76    inference(resolution,[],[f192,f269])).
% 10.31/1.76  fof(f192,plain,(
% 10.31/1.76    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 10.31/1.76    inference(cnf_transformation,[],[f119])).
% 10.31/1.76  fof(f5064,plain,(
% 10.31/1.76    ~spl16_3 | spl16_4),
% 10.31/1.76    inference(avatar_split_clause,[],[f2541,f287,f283])).
% 10.93/1.76  fof(f2541,plain,(
% 10.93/1.76    r1_tarski(sK8,u1_struct_0(sK7)) | ~v1_xboole_0(u1_struct_0(sK7))),
% 10.93/1.76    inference(superposition,[],[f269,f253])).
% 10.93/1.76  fof(f2515,plain,(
% 10.93/1.76    spl16_45),
% 10.93/1.76    inference(avatar_contradiction_clause,[],[f2514])).
% 10.93/1.76  fof(f2514,plain,(
% 10.93/1.76    $false | spl16_45),
% 10.93/1.76    inference(subsumption_resolution,[],[f2513,f130])).
% 10.93/1.76  fof(f2513,plain,(
% 10.93/1.76    ~v2_pre_topc(sK6) | spl16_45),
% 10.93/1.76    inference(subsumption_resolution,[],[f2512,f131])).
% 10.93/1.76  fof(f2512,plain,(
% 10.93/1.76    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | spl16_45),
% 10.93/1.76    inference(resolution,[],[f2494,f163])).
% 10.93/1.76  fof(f163,plain,(
% 10.93/1.76    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 10.93/1.76    inference(cnf_transformation,[],[f48])).
% 10.93/1.76  fof(f48,plain,(
% 10.93/1.76    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 10.93/1.76    inference(flattening,[],[f47])).
% 10.93/1.76  fof(f47,plain,(
% 10.93/1.76    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 10.93/1.76    inference(ennf_transformation,[],[f32])).
% 10.93/1.76  fof(f32,axiom,(
% 10.93/1.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 10.93/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 10.93/1.76  fof(f2494,plain,(
% 10.93/1.76    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | spl16_45),
% 10.93/1.76    inference(avatar_component_clause,[],[f2492])).
% 10.93/1.76  fof(f2391,plain,(
% 10.93/1.76    spl16_41),
% 10.93/1.76    inference(avatar_contradiction_clause,[],[f2390])).
% 10.93/1.76  fof(f2390,plain,(
% 10.93/1.76    $false | spl16_41),
% 10.93/1.76    inference(subsumption_resolution,[],[f2389,f132])).
% 10.93/1.76  fof(f2389,plain,(
% 10.93/1.76    ~v2_pre_topc(sK7) | spl16_41),
% 10.93/1.76    inference(subsumption_resolution,[],[f2388,f133])).
% 10.93/1.76  fof(f2388,plain,(
% 10.93/1.76    ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | spl16_41),
% 10.93/1.76    inference(resolution,[],[f2372,f163])).
% 10.93/1.76  fof(f2372,plain,(
% 10.93/1.76    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | spl16_41),
% 10.93/1.76    inference(avatar_component_clause,[],[f2370])).
% 10.93/1.76  fof(f2385,plain,(
% 10.93/1.76    ~spl16_41 | ~spl16_42 | ~spl16_43 | spl16_44 | ~spl16_2 | ~spl16_39),
% 10.93/1.76    inference(avatar_split_clause,[],[f2368,f2323,f242,f2382,f2378,f2374,f2370])).
% 10.93/1.76  fof(f2368,plain,(
% 10.93/1.76    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | (~spl16_2 | ~spl16_39)),
% 10.93/1.76    inference(subsumption_resolution,[],[f2367,f130])).
% 10.93/1.76  fof(f2367,plain,(
% 10.93/1.76    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(sK6) | (~spl16_2 | ~spl16_39)),
% 10.93/1.76    inference(subsumption_resolution,[],[f2366,f131])).
% 10.93/1.76  fof(f2366,plain,(
% 10.93/1.76    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (~spl16_2 | ~spl16_39)),
% 10.93/1.76    inference(subsumption_resolution,[],[f2365,f2324])).
% 10.93/1.76  fof(f2324,plain,(
% 10.93/1.76    l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~spl16_39),
% 10.93/1.76    inference(avatar_component_clause,[],[f2323])).
% 10.93/1.76  fof(f2365,plain,(
% 10.93/1.76    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_2),
% 10.93/1.76    inference(subsumption_resolution,[],[f2364,f134])).
% 10.93/1.76  fof(f2364,plain,(
% 10.93/1.76    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_2),
% 10.93/1.76    inference(subsumption_resolution,[],[f2363,f256])).
% 10.93/1.76  fof(f2363,plain,(
% 10.93/1.76    v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~spl16_2),
% 10.93/1.76    inference(subsumption_resolution,[],[f2357,f255])).
% 10.93/1.76  fof(f2357,plain,(
% 10.93/1.76    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6)),
% 10.93/1.76    inference(resolution,[],[f234,f259])).
% 10.93/1.76  fof(f2343,plain,(
% 10.93/1.76    spl16_39),
% 10.93/1.76    inference(avatar_contradiction_clause,[],[f2342])).
% 10.93/1.76  fof(f2342,plain,(
% 10.93/1.76    $false | spl16_39),
% 10.93/1.76    inference(subsumption_resolution,[],[f2340,f133])).
% 10.93/1.76  fof(f2340,plain,(
% 10.93/1.76    ~l1_pre_topc(sK7) | spl16_39),
% 10.93/1.76    inference(resolution,[],[f2325,f614])).
% 10.93/1.76  fof(f614,plain,(
% 10.93/1.76    ( ! [X0] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 10.93/1.76    inference(resolution,[],[f182,f147])).
% 10.93/1.76  fof(f147,plain,(
% 10.93/1.76    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 10.93/1.76    inference(cnf_transformation,[],[f39])).
% 10.93/1.76  fof(f39,plain,(
% 10.93/1.76    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 10.93/1.76    inference(ennf_transformation,[],[f31])).
% 10.93/1.76  fof(f31,axiom,(
% 10.93/1.76    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 10.93/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 10.93/1.76  fof(f182,plain,(
% 10.93/1.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 10.93/1.76    inference(cnf_transformation,[],[f60])).
% 10.93/1.76  fof(f60,plain,(
% 10.93/1.76    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 10.93/1.76    inference(ennf_transformation,[],[f30])).
% 10.93/1.76  fof(f30,axiom,(
% 10.93/1.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 10.93/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 10.93/1.76  fof(f2325,plain,(
% 10.93/1.76    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | spl16_39),
% 10.93/1.76    inference(avatar_component_clause,[],[f2323])).
% 10.93/1.76  fof(f2339,plain,(
% 10.93/1.76    spl16_38),
% 10.93/1.76    inference(avatar_contradiction_clause,[],[f2338])).
% 10.93/1.76  fof(f2338,plain,(
% 10.93/1.76    $false | spl16_38),
% 10.93/1.76    inference(subsumption_resolution,[],[f2336,f131])).
% 10.93/1.76  fof(f2336,plain,(
% 10.93/1.76    ~l1_pre_topc(sK6) | spl16_38),
% 10.93/1.76    inference(resolution,[],[f2321,f614])).
% 10.93/1.76  fof(f2321,plain,(
% 10.93/1.76    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | spl16_38),
% 10.93/1.76    inference(avatar_component_clause,[],[f2319])).
% 10.93/1.76  fof(f464,plain,(
% 10.93/1.76    spl16_23),
% 10.93/1.76    inference(avatar_contradiction_clause,[],[f463])).
% 10.93/1.76  fof(f463,plain,(
% 10.93/1.76    $false | spl16_23),
% 10.93/1.76    inference(subsumption_resolution,[],[f462,f143])).
% 10.93/1.76  fof(f462,plain,(
% 10.93/1.76    ~v1_xboole_0(k1_xboole_0) | spl16_23),
% 10.93/1.76    inference(subsumption_resolution,[],[f458,f456])).
% 10.93/1.76  fof(f456,plain,(
% 10.93/1.76    ( ! [X0,X1] : (~v1_xboole_0(sK15(X0,X1))) ) | spl16_23),
% 10.93/1.76    inference(resolution,[],[f445,f210])).
% 10.93/1.76  fof(f445,plain,(
% 10.93/1.76    ( ! [X0] : (~v1_funct_1(X0) | ~v1_xboole_0(X0)) ) | spl16_23),
% 10.93/1.76    inference(superposition,[],[f407,f155])).
% 10.93/1.76  fof(f407,plain,(
% 10.93/1.76    ~v1_funct_1(k1_xboole_0) | spl16_23),
% 10.93/1.76    inference(avatar_component_clause,[],[f405])).
% 10.93/1.76  fof(f458,plain,(
% 10.93/1.76    ( ! [X0] : (v1_xboole_0(sK15(X0,k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)) )),
% 10.93/1.76    inference(resolution,[],[f428,f157])).
% 10.93/1.76  fof(f157,plain,(
% 10.93/1.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 10.93/1.76    inference(cnf_transformation,[],[f44])).
% 10.93/1.76  fof(f44,plain,(
% 10.93/1.76    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 10.93/1.76    inference(ennf_transformation,[],[f10])).
% 10.93/1.76  fof(f10,axiom,(
% 10.93/1.76    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 10.93/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 10.93/1.76  fof(f443,plain,(
% 10.93/1.76    spl16_22),
% 10.93/1.76    inference(avatar_contradiction_clause,[],[f442])).
% 10.93/1.76  fof(f442,plain,(
% 10.93/1.76    $false | spl16_22),
% 10.93/1.76    inference(subsumption_resolution,[],[f437,f143])).
% 10.93/1.76  fof(f437,plain,(
% 10.93/1.76    ~v1_xboole_0(k1_xboole_0) | spl16_22),
% 10.93/1.76    inference(superposition,[],[f433,f232])).
% 10.93/1.76  fof(f433,plain,(
% 10.93/1.76    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | spl16_22),
% 10.93/1.76    inference(subsumption_resolution,[],[f426,f414])).
% 10.93/1.76  fof(f414,plain,(
% 10.93/1.76    ( ! [X0,X1] : (~v1_xboole_0(sK15(X0,X1))) ) | spl16_22),
% 10.93/1.76    inference(resolution,[],[f409,f207])).
% 10.93/1.76  fof(f207,plain,(
% 10.93/1.76    ( ! [X0,X1] : (v1_relat_1(sK15(X0,X1))) )),
% 10.93/1.76    inference(cnf_transformation,[],[f129])).
% 10.93/1.76  fof(f409,plain,(
% 10.93/1.76    ( ! [X0] : (~v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | spl16_22),
% 10.93/1.76    inference(superposition,[],[f403,f155])).
% 10.93/1.76  fof(f403,plain,(
% 10.93/1.76    ~v1_relat_1(k1_xboole_0) | spl16_22),
% 10.93/1.76    inference(avatar_component_clause,[],[f401])).
% 10.93/1.76  fof(f426,plain,(
% 10.93/1.76    ( ! [X0,X1] : (v1_xboole_0(sK15(X0,X1)) | ~v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 10.93/1.76    inference(resolution,[],[f206,f157])).
% 10.93/1.76  fof(f246,plain,(
% 10.93/1.76    spl16_1 | spl16_2),
% 10.93/1.76    inference(avatar_split_clause,[],[f141,f242,f238])).
% 10.93/1.76  fof(f141,plain,(
% 10.93/1.76    v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)),
% 10.93/1.76    inference(cnf_transformation,[],[f92])).
% 10.93/1.76  fof(f245,plain,(
% 10.93/1.76    ~spl16_1 | ~spl16_2),
% 10.93/1.76    inference(avatar_split_clause,[],[f142,f242,f238])).
% 10.93/1.76  fof(f142,plain,(
% 10.93/1.76    ~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)),
% 10.93/1.76    inference(cnf_transformation,[],[f92])).
% 10.93/1.76  % SZS output end Proof for theBenchmark
% 10.93/1.76  % (9981)------------------------------
% 10.93/1.76  % (9981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.93/1.76  % (9981)Termination reason: Refutation
% 10.93/1.76  
% 10.93/1.76  % (9981)Memory used [KB]: 13432
% 10.93/1.76  % (9981)Time elapsed: 1.291 s
% 10.93/1.76  % (9981)------------------------------
% 10.93/1.76  % (9981)------------------------------
% 10.93/1.76  % (9953)Success in time 1.405 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0916+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 612 expanded)
%              Number of leaves         :   50 ( 258 expanded)
%              Depth                    :   11
%              Number of atoms          :  684 (2711 expanded)
%              Number of equality atoms :  208 ( 483 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f568,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f149,f172,f235,f260,f270,f317,f329,f341,f384,f388,f398,f408,f410,f420,f428,f443,f455,f502,f505,f509,f510,f511,f515,f523,f528,f540,f546,f556,f559,f564,f567])).

fof(f567,plain,
    ( ~ spl8_32
    | spl8_37
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f565,f554,f562,f452])).

fof(f452,plain,
    ( spl8_32
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f562,plain,
    ( spl8_37
  <=> m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f554,plain,
    ( spl8_36
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f565,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_36 ),
    inference(superposition,[],[f55,f555])).

fof(f555,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f554])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f564,plain,
    ( ~ spl8_37
    | spl8_24
    | spl8_3 ),
    inference(avatar_split_clause,[],[f560,f82,f253,f562])).

fof(f253,plain,
    ( spl8_24
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f82,plain,
    ( spl8_3
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f560,plain,
    ( v1_xboole_0(sK5)
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_3 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f83,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f559,plain,
    ( ~ spl8_32
    | spl8_35
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f557,f467,f526,f452])).

fof(f526,plain,
    ( spl8_35
  <=> m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f467,plain,
    ( spl8_33
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f557,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_33 ),
    inference(superposition,[],[f57,f468])).

fof(f468,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f467])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f556,plain,
    ( spl8_36
    | spl8_27
    | spl8_26
    | spl8_25
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f549,f130,f285,f288,f291,f554])).

fof(f291,plain,
    ( spl8_27
  <=> o_0_0_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f288,plain,
    ( spl8_26
  <=> o_0_0_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f285,plain,
    ( spl8_25
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f130,plain,
    ( spl8_15
  <=> ! [X7,X8,X6] :
        ( k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(X6,X7,X8,sK6)
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | o_0_0_xboole_0 = X8
        | ~ m1_subset_1(sK6,k3_zfmisc_1(X6,X7,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f549,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_15 ),
    inference(resolution,[],[f131,f134])).

fof(f134,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(resolution,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f41,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f131,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK6,k3_zfmisc_1(X6,X7,X8))
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | o_0_0_xboole_0 = X8
        | k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(X6,X7,X8,sK6) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f546,plain,
    ( spl8_33
    | spl8_27
    | spl8_26
    | spl8_25
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f542,f126,f285,f288,f291,f467])).

fof(f126,plain,
    ( spl8_14
  <=> ! [X3,X5,X4] :
        ( k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(X3,X4,X5,sK6)
        | o_0_0_xboole_0 = X3
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | ~ m1_subset_1(sK6,k3_zfmisc_1(X3,X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f542,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_14 ),
    inference(resolution,[],[f127,f134])).

fof(f127,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK6,k3_zfmisc_1(X3,X4,X5))
        | o_0_0_xboole_0 = X3
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(X3,X4,X5,sK6) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f540,plain,
    ( spl8_31
    | spl8_27
    | spl8_26
    | spl8_25
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f536,f122,f285,f288,f291,f358])).

fof(f358,plain,
    ( spl8_31
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f122,plain,
    ( spl8_13
  <=> ! [X1,X0,X2] :
        ( k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(X0,X1,X2,sK6)
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | ~ m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f536,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_13 ),
    inference(resolution,[],[f123,f134])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2))
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(X0,X1,X2,sK6) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f528,plain,
    ( ~ spl8_35
    | spl8_21
    | spl8_2 ),
    inference(avatar_split_clause,[],[f524,f79,f187,f526])).

fof(f187,plain,
    ( spl8_21
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f79,plain,
    ( spl8_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f524,plain,
    ( v1_xboole_0(sK4)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_2 ),
    inference(resolution,[],[f80,f48])).

fof(f80,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f523,plain,(
    spl8_32 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl8_32 ),
    inference(subsumption_resolution,[],[f134,f453])).

fof(f453,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f452])).

fof(f515,plain,
    ( ~ spl8_16
    | spl8_17
    | spl8_1 ),
    inference(avatar_split_clause,[],[f514,f76,f140,f137])).

fof(f137,plain,
    ( spl8_16
  <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f140,plain,
    ( spl8_17
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f76,plain,
    ( spl8_1
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f514,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_1 ),
    inference(resolution,[],[f77,f48])).

fof(f77,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f511,plain,
    ( spl8_10
    | spl8_11
    | spl8_12
    | spl8_15 ),
    inference(avatar_split_clause,[],[f508,f130,f119,f116,f113])).

fof(f113,plain,
    ( spl8_10
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f116,plain,
    ( spl8_11
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f119,plain,
    ( spl8_12
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f508,plain,(
    ! [X6,X8,X7] :
      ( k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(X6,X7,X8,sK6)
      | ~ m1_subset_1(sK6,k3_zfmisc_1(X6,X7,X8))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X8
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6 ) ),
    inference(resolution,[],[f40,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | k7_mcart_1(X3,X4,X5,X7) = k7_mcart_1(X0,X1,X2,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f44,f44,f44,f44,f44,f44])).

fof(f44,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ! [X6] :
          ( ! [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
              | X6 != X7
              | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( ? [X6] :
            ( ? [X7] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                    & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                    & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_mcart_1)).

fof(f40,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f510,plain,
    ( spl8_10
    | spl8_11
    | spl8_12
    | spl8_14 ),
    inference(avatar_split_clause,[],[f507,f126,f119,f116,f113])).

fof(f507,plain,(
    ! [X4,X5,X3] :
      ( k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(X3,X4,X5,sK6)
      | ~ m1_subset_1(sK6,k3_zfmisc_1(X3,X4,X5))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3 ) ),
    inference(resolution,[],[f40,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | k6_mcart_1(X3,X4,X5,X7) = k6_mcart_1(X0,X1,X2,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f44,f44,f44,f44,f44,f44])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f509,plain,
    ( spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f506,f122,f119,f116,f113])).

fof(f506,plain,(
    ! [X2,X0,X1] :
      ( k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(X0,X1,X2,sK6)
      | ~ m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | k5_mcart_1(X3,X4,X5,X7) = k5_mcart_1(X0,X1,X2,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f44,f44,f44,f44,f44,f44])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f505,plain,
    ( spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f504,f106,f103])).

fof(f103,plain,
    ( spl8_8
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f106,plain,
    ( spl8_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f504,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f39,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f502,plain,(
    ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f43,f496])).

fof(f496,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f491,f69])).

fof(f69,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f53,f44,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f491,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(sK3,sK4,o_0_0_xboole_0))
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f133,f473])).

fof(f473,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl8_24 ),
    inference(resolution,[],[f254,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f254,plain,
    ( v1_xboole_0(sK5)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f133,plain,(
    ~ v1_xboole_0(k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

% (29112)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f455,plain,
    ( ~ spl8_32
    | spl8_16
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f450,f358,f137,f452])).

fof(f450,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_31 ),
    inference(superposition,[],[f56,f359])).

fof(f359,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f358])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f443,plain,(
    ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl8_23 ),
    inference(resolution,[],[f251,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f6,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f251,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK5)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl8_23
  <=> ! [X0] : ~ m1_subset_1(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f428,plain,
    ( spl8_9
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl8_9
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f43,f424])).

fof(f424,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl8_9
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f107,f120])).

fof(f120,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f107,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f420,plain,
    ( spl8_23
    | spl8_24
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f419,f103,f253,f250])).

fof(f419,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK5)
        | ~ m1_subset_1(X0,sK5) )
    | ~ spl8_8 ),
    inference(resolution,[],[f104,f48])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f410,plain,
    ( spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f409,f90,f87])).

fof(f87,plain,
    ( spl8_4
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f90,plain,
    ( spl8_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f409,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f37,f54])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f408,plain,(
    ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl8_22 ),
    inference(resolution,[],[f200,f46])).

fof(f200,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK3)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl8_22
  <=> ! [X0] : ~ m1_subset_1(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f398,plain,
    ( spl8_22
    | spl8_17
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f397,f87,f140,f199])).

fof(f397,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl8_4 ),
    inference(resolution,[],[f88,f48])).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f388,plain,
    ( spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f387,f98,f95])).

fof(f95,plain,
    ( spl8_6
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f98,plain,
    ( spl8_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f387,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f38,f54])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f384,plain,(
    ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f43,f379])).

fof(f379,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f376,f70])).

fof(f70,plain,(
    ! [X2,X0] : o_0_0_xboole_0 = k3_zfmisc_1(X0,o_0_0_xboole_0,X2) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f52,f44,f44])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f376,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(sK3,o_0_0_xboole_0,sK5))
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f133,f362])).

fof(f362,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl8_21 ),
    inference(resolution,[],[f188,f61])).

fof(f188,plain,
    ( v1_xboole_0(sK4)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f341,plain,(
    ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f43,f337])).

fof(f337,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_27 ),
    inference(resolution,[],[f336,f49])).

fof(f336,plain,
    ( r2_hidden(sK6,o_0_0_xboole_0)
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f334,f69])).

fof(f334,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,o_0_0_xboole_0))
    | ~ spl8_27 ),
    inference(backward_demodulation,[],[f41,f292])).

fof(f292,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f291])).

fof(f329,plain,(
    ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f43,f324])).

fof(f324,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_26 ),
    inference(resolution,[],[f323,f49])).

fof(f323,plain,
    ( r2_hidden(sK6,o_0_0_xboole_0)
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f322,f70])).

fof(f322,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(sK3,o_0_0_xboole_0,sK5))
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f41,f289])).

fof(f289,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f288])).

fof(f317,plain,(
    ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f43,f311])).

fof(f311,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f306,f71])).

fof(f71,plain,(
    ! [X2,X1] : o_0_0_xboole_0 = k3_zfmisc_1(o_0_0_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f51,f44,f44])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f306,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(o_0_0_xboole_0,sK4,sK5))
    | ~ spl8_25 ),
    inference(backward_demodulation,[],[f133,f286])).

fof(f286,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f270,plain,(
    ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl8_20 ),
    inference(resolution,[],[f185,f46])).

fof(f185,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_20
  <=> ! [X0] : ~ m1_subset_1(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f260,plain,
    ( spl8_20
    | spl8_21
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f259,f95,f187,f184])).

fof(f259,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4)
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f48])).

fof(f96,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f235,plain,(
    ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f43,f231])).

fof(f231,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_17 ),
    inference(resolution,[],[f230,f49])).

fof(f230,plain,
    ( r2_hidden(sK6,o_0_0_xboole_0)
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f229,f71])).

fof(f229,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(o_0_0_xboole_0,sK4,sK5))
    | ~ spl8_17 ),
    inference(backward_demodulation,[],[f41,f218])).

fof(f218,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl8_17 ),
    inference(resolution,[],[f141,f61])).

fof(f141,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f172,plain,
    ( spl8_7
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl8_7
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f43,f163])).

fof(f163,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl8_7
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f99,f117])).

fof(f117,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f99,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f149,plain,
    ( spl8_5
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl8_5
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f43,f145])).

fof(f145,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl8_5
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f91,f114])).

fof(f114,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f84,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f42,f82,f79,f76])).

fof(f42,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t87_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  281 ( 853 expanded)
%              Number of leaves         :   66 ( 379 expanded)
%              Depth                    :   11
%              Number of atoms          :  958 (4543 expanded)
%              Number of equality atoms :  317 ( 785 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f199,f227,f244,f253,f297,f331,f343,f362,f365,f423,f439,f456,f528,f545,f563,f578,f616,f632,f637,f649,f663,f666,f678,f698,f699,f700,f701,f703,f709,f722,f732,f760,f765,f767,f772,f777,f786,f787,f796,f801,f806])).

fof(f806,plain,
    ( ~ spl10_99
    | spl10_104
    | ~ spl10_96 ),
    inference(avatar_split_clause,[],[f802,f750,f804,f755])).

fof(f755,plain,
    ( spl10_99
  <=> ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f804,plain,
    ( spl10_104
  <=> m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f750,plain,
    ( spl10_96
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f802,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_96 ),
    inference(superposition,[],[f75,f751])).

fof(f751,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f750])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k11_mcart_1)).

fof(f801,plain,
    ( ~ spl10_105
    | spl10_60
    | spl10_7 ),
    inference(avatar_split_clause,[],[f797,f111,f381,f799])).

fof(f799,plain,
    ( spl10_105
  <=> ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f381,plain,
    ( spl10_60
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f111,plain,
    ( spl10_7
  <=> ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f797,plain,
    ( v1_xboole_0(sK7)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ spl10_7 ),
    inference(resolution,[],[f112,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t2_subset)).

fof(f112,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f796,plain,
    ( ~ spl10_99
    | spl10_102
    | ~ spl10_94 ),
    inference(avatar_split_clause,[],[f792,f740,f794,f755])).

fof(f794,plain,
    ( spl10_102
  <=> m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f740,plain,
    ( spl10_94
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f792,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_94 ),
    inference(superposition,[],[f77,f741])).

fof(f741,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f740])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k10_mcart_1)).

fof(f787,plain,
    ( spl10_94
    | spl10_76
    | spl10_74
    | spl10_72
    | spl10_70
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f779,f175,f475,f478,f481,f484,f740])).

fof(f484,plain,
    ( spl10_76
  <=> o_0_0_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f481,plain,
    ( spl10_74
  <=> o_0_0_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f478,plain,
    ( spl10_72
  <=> o_0_0_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f475,plain,
    ( spl10_70
  <=> o_0_0_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f175,plain,
    ( spl10_36
  <=> ! [X9,X11,X8,X10] :
        ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(X8,X9,X10,X11,sK8)
        | o_0_0_xboole_0 = X8
        | o_0_0_xboole_0 = X9
        | o_0_0_xboole_0 = X10
        | o_0_0_xboole_0 = X11
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X8,X9,X10,X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f779,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_36 ),
    inference(resolution,[],[f183,f176])).

fof(f176,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X8,X9,X10,X11))
        | o_0_0_xboole_0 = X8
        | o_0_0_xboole_0 = X9
        | o_0_0_xboole_0 = X10
        | o_0_0_xboole_0 = X11
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(X8,X9,X10,X11,sK8) )
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f175])).

fof(f183,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t1_subset)).

fof(f57,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f26,f46,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK5)
                      | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                    & r2_hidden(X8,k4_zfmisc_1(X4,sK5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                & m1_subset_1(X7,k1_zfmisc_1(X3)) )
            & m1_subset_1(X6,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                    | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                  & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
              & m1_subset_1(X7,k1_zfmisc_1(X3)) )
          & m1_subset_1(X6,k1_zfmisc_1(X2)) )
     => ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK6)
                  | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                  | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
            & m1_subset_1(X7,k1_zfmisc_1(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
              & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
          & m1_subset_1(X7,k1_zfmisc_1(X3)) )
     => ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK7)
              | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
              | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
              | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
            & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK7))
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
            | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
            | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
            | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
          & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK8),X7)
          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK8),X6)
          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK8),X5)
          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK8),X4) )
        & r2_hidden(sK8,k4_zfmisc_1(X4,X5,X6,X7))
        & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t87_mcart_1)).

fof(f786,plain,
    ( spl10_96
    | spl10_76
    | spl10_74
    | spl10_72
    | spl10_70
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f778,f179,f475,f478,f481,f484,f750])).

fof(f179,plain,
    ( spl10_38
  <=> ! [X13,X15,X12,X14] :
        ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(X12,X13,X14,X15,sK8)
        | o_0_0_xboole_0 = X12
        | o_0_0_xboole_0 = X13
        | o_0_0_xboole_0 = X14
        | o_0_0_xboole_0 = X15
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X12,X13,X14,X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f778,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_38 ),
    inference(resolution,[],[f183,f180])).

fof(f180,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X12,X13,X14,X15))
        | o_0_0_xboole_0 = X12
        | o_0_0_xboole_0 = X13
        | o_0_0_xboole_0 = X14
        | o_0_0_xboole_0 = X15
        | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(X12,X13,X14,X15,sK8) )
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f179])).

fof(f777,plain,
    ( ~ spl10_103
    | spl10_48
    | spl10_5 ),
    inference(avatar_split_clause,[],[f773,f108,f261,f775])).

fof(f775,plain,
    ( spl10_103
  <=> ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f261,plain,
    ( spl10_48
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f108,plain,
    ( spl10_5
  <=> ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f773,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ spl10_5 ),
    inference(resolution,[],[f109,f65])).

fof(f109,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f772,plain,
    ( ~ spl10_101
    | spl10_54
    | spl10_3 ),
    inference(avatar_split_clause,[],[f768,f105,f319,f770])).

fof(f770,plain,
    ( spl10_101
  <=> ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f319,plain,
    ( spl10_54
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f105,plain,
    ( spl10_3
  <=> ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f768,plain,
    ( v1_xboole_0(sK5)
    | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ spl10_3 ),
    inference(resolution,[],[f106,f65])).

fof(f106,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f767,plain,(
    spl10_99 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f183,f756])).

fof(f756,plain,
    ( ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f755])).

fof(f765,plain,
    ( ~ spl10_99
    | spl10_100
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f761,f730,f763,f755])).

fof(f763,plain,
    ( spl10_100
  <=> m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f730,plain,
    ( spl10_92
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f761,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_92 ),
    inference(superposition,[],[f78,f731])).

fof(f731,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f730])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k9_mcart_1)).

fof(f760,plain,
    ( ~ spl10_99
    | spl10_40
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f753,f611,f758,f755])).

fof(f758,plain,
    ( spl10_40
  <=> m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f611,plain,
    ( spl10_90
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f753,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_90 ),
    inference(superposition,[],[f76,f612])).

fof(f612,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_90 ),
    inference(avatar_component_clause,[],[f611])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k8_mcart_1)).

fof(f732,plain,
    ( spl10_92
    | spl10_76
    | spl10_74
    | spl10_72
    | spl10_70
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f723,f171,f475,f478,f481,f484,f730])).

fof(f171,plain,
    ( spl10_34
  <=> ! [X5,X7,X4,X6] :
        ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(X4,X5,X6,X7,sK8)
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f723,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_34 ),
    inference(resolution,[],[f172,f183])).

fof(f172,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X4,X5,X6,X7))
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(X4,X5,X6,X7,sK8) )
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f171])).

fof(f722,plain,
    ( spl10_90
    | spl10_76
    | spl10_74
    | spl10_72
    | spl10_70
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f716,f167,f475,f478,f481,f484,f611])).

fof(f167,plain,
    ( spl10_32
  <=> ! [X1,X3,X0,X2] :
        ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(X0,X1,X2,X3,sK8)
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 = X3
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f716,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_32 ),
    inference(resolution,[],[f168,f183])).

fof(f168,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3))
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 = X3
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(X0,X1,X2,X3,sK8) )
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f167])).

fof(f709,plain,(
    ~ spl10_58 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl10_58 ),
    inference(resolution,[],[f379,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f14,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',existence_m1_subset_1)).

fof(f379,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK7)
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl10_58
  <=> ! [X0] : ~ m1_subset_1(X0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f703,plain,
    ( ~ spl10_41
    | spl10_42
    | spl10_1 ),
    inference(avatar_split_clause,[],[f702,f102,f190,f187])).

fof(f187,plain,
    ( spl10_41
  <=> ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f190,plain,
    ( spl10_42
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f102,plain,
    ( spl10_1
  <=> ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f702,plain,
    ( v1_xboole_0(sK4)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ spl10_1 ),
    inference(resolution,[],[f103,f65])).

fof(f103,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f701,plain,
    ( spl10_24
    | spl10_26
    | spl10_28
    | spl10_30
    | spl10_38 ),
    inference(avatar_split_clause,[],[f697,f179,f164,f161,f158,f155])).

fof(f155,plain,
    ( spl10_24
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f158,plain,
    ( spl10_26
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f161,plain,
    ( spl10_28
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f164,plain,
    ( spl10_30
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f697,plain,(
    ! [X14,X12,X15,X13] :
      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(X12,X13,X14,X15,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X12,X13,X14,X15))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X15
      | o_0_0_xboole_0 = X14
      | o_0_0_xboole_0 = X13
      | o_0_0_xboole_0 = X12 ) ),
    inference(resolution,[],[f56,f97])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k11_mcart_1(X0,X1,X2,X3,X9) = k11_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f82,f60,f60,f60,f60,f60,f60,f60,f60])).

fof(f60,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',d2_xboole_0)).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ! [X8] :
          ( ! [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
              | X8 != X9
              | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ~ ( ? [X8] :
            ( ? [X9] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                    & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                    & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                    & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t86_mcart_1)).

fof(f56,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f700,plain,
    ( spl10_24
    | spl10_26
    | spl10_28
    | spl10_30
    | spl10_36 ),
    inference(avatar_split_clause,[],[f696,f175,f164,f161,f158,f155])).

fof(f696,plain,(
    ! [X10,X8,X11,X9] :
      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(X8,X9,X10,X11,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X8,X9,X10,X11))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X11
      | o_0_0_xboole_0 = X10
      | o_0_0_xboole_0 = X9
      | o_0_0_xboole_0 = X8 ) ),
    inference(resolution,[],[f56,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k10_mcart_1(X0,X1,X2,X3,X9) = k10_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f81,f60,f60,f60,f60,f60,f60,f60,f60])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f699,plain,
    ( spl10_24
    | spl10_26
    | spl10_28
    | spl10_30
    | spl10_34 ),
    inference(avatar_split_clause,[],[f695,f171,f164,f161,f158,f155])).

fof(f695,plain,(
    ! [X6,X4,X7,X5] :
      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(X4,X5,X6,X7,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X4,X5,X6,X7))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4 ) ),
    inference(resolution,[],[f56,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k9_mcart_1(X0,X1,X2,X3,X9) = k9_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f80,f60,f60,f60,f60,f60,f60,f60,f60])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f698,plain,
    ( spl10_24
    | spl10_26
    | spl10_28
    | spl10_30
    | spl10_32 ),
    inference(avatar_split_clause,[],[f694,f167,f164,f161,f158,f155])).

fof(f694,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(X0,X1,X2,X3,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f56,f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k8_mcart_1(X0,X1,X2,X3,X9) = k8_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f60,f60,f60,f60,f60,f60,f60,f60])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f678,plain,
    ( spl10_58
    | spl10_60
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f677,f144,f381,f378])).

fof(f144,plain,
    ( spl10_20
  <=> ! [X0] : ~ r2_hidden(X0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f677,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK7)
        | ~ m1_subset_1(X0,sK7) )
    | ~ spl10_20 ),
    inference(resolution,[],[f145,f65])).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK7)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f144])).

fof(f666,plain,
    ( spl10_12
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f664,f129,f126])).

fof(f126,plain,
    ( spl10_12
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f129,plain,
    ( spl10_15
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f664,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t5_subset)).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f663,plain,(
    ~ spl10_52 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | ~ spl10_52 ),
    inference(resolution,[],[f317,f62])).

fof(f317,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK5)
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl10_52
  <=> ! [X0] : ~ m1_subset_1(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f649,plain,
    ( spl10_52
    | spl10_54
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f648,f126,f319,f316])).

fof(f648,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK5)
        | ~ m1_subset_1(X0,sK5) )
    | ~ spl10_12 ),
    inference(resolution,[],[f127,f65])).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f637,plain,
    ( spl10_8
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f635,f120,f117])).

fof(f117,plain,
    ( spl10_8
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f120,plain,
    ( spl10_11
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f635,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f52,f69])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f632,plain,(
    ~ spl10_50 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl10_50 ),
    inference(resolution,[],[f280,f62])).

fof(f280,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl10_50
  <=> ! [X0] : ~ m1_subset_1(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f616,plain,
    ( spl10_50
    | spl10_42
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f615,f117,f190,f279])).

fof(f615,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4)
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl10_8 ),
    inference(resolution,[],[f118,f65])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f578,plain,(
    ~ spl10_76 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f59,f574])).

fof(f574,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_76 ),
    inference(resolution,[],[f573,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t7_boole)).

fof(f573,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_76 ),
    inference(forward_demodulation,[],[f572,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k4_zfmisc_1(X0,X1,X2,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f74,f60,f60])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t55_mcart_1)).

fof(f572,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,o_0_0_xboole_0))
    | ~ spl10_76 ),
    inference(forward_demodulation,[],[f57,f485])).

fof(f485,plain,
    ( o_0_0_xboole_0 = sK7
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f484])).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_o_0_0_xboole_0)).

fof(f563,plain,(
    ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f59,f557])).

fof(f557,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_74 ),
    inference(resolution,[],[f556,f67])).

fof(f556,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_74 ),
    inference(forward_demodulation,[],[f553,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] : k4_zfmisc_1(X0,X1,o_0_0_xboole_0,X3) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f73,f60,f60])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f553,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,o_0_0_xboole_0,sK7))
    | ~ spl10_74 ),
    inference(backward_demodulation,[],[f482,f57])).

fof(f482,plain,
    ( o_0_0_xboole_0 = sK6
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f481])).

fof(f545,plain,(
    ~ spl10_72 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f59,f539])).

fof(f539,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_72 ),
    inference(resolution,[],[f538,f67])).

fof(f538,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_72 ),
    inference(forward_demodulation,[],[f537,f95])).

fof(f95,plain,(
    ! [X2,X0,X3] : k4_zfmisc_1(X0,o_0_0_xboole_0,X2,X3) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X1
      | k4_zfmisc_1(X0,X1,X2,X3) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f72,f60,f60])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f537,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,o_0_0_xboole_0,sK6,sK7))
    | ~ spl10_72 ),
    inference(forward_demodulation,[],[f57,f479])).

fof(f479,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f478])).

fof(f528,plain,(
    ~ spl10_70 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f59,f519])).

fof(f519,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f514,f96])).

fof(f96,plain,(
    ! [X2,X3,X1] : k4_zfmisc_1(o_0_0_xboole_0,X1,X2,X3) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f71,f60,f60])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f514,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(o_0_0_xboole_0,sK5,sK6,sK7))
    | ~ spl10_70 ),
    inference(backward_demodulation,[],[f476,f182])).

fof(f182,plain,(
    ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(resolution,[],[f57,f67])).

fof(f476,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f475])).

fof(f456,plain,(
    ~ spl10_60 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f59,f452])).

fof(f452,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_60 ),
    inference(resolution,[],[f451,f67])).

fof(f451,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f450,f93])).

fof(f450,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,o_0_0_xboole_0))
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f57,f409])).

fof(f409,plain,
    ( o_0_0_xboole_0 = sK7
    | ~ spl10_60 ),
    inference(resolution,[],[f382,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t6_boole)).

fof(f382,plain,
    ( v1_xboole_0(sK7)
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f381])).

fof(f439,plain,(
    ~ spl10_54 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f59,f435])).

fof(f435,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_54 ),
    inference(resolution,[],[f434,f67])).

fof(f434,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f433,f95])).

fof(f433,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,o_0_0_xboole_0,sK6,sK7))
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f57,f407])).

fof(f407,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl10_54 ),
    inference(resolution,[],[f320,f83])).

fof(f320,plain,
    ( v1_xboole_0(sK5)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f319])).

fof(f423,plain,(
    ~ spl10_48 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f59,f415])).

fof(f415,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f410,f94])).

fof(f410,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,o_0_0_xboole_0,sK7))
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f400,f182])).

fof(f400,plain,
    ( o_0_0_xboole_0 = sK6
    | ~ spl10_48 ),
    inference(resolution,[],[f262,f83])).

fof(f262,plain,
    ( v1_xboole_0(sK6)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f261])).

fof(f365,plain,
    ( spl10_16
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f363,f138,f135])).

fof(f135,plain,
    ( spl10_16
  <=> ! [X0] : ~ r2_hidden(X0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f138,plain,
    ( spl10_19
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f363,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f54,f69])).

fof(f54,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f362,plain,(
    ~ spl10_46 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl10_46 ),
    inference(resolution,[],[f259,f62])).

fof(f259,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK6)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl10_46
  <=> ! [X0] : ~ m1_subset_1(X0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f343,plain,
    ( spl10_46
    | spl10_48
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f342,f135,f261,f258])).

fof(f342,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK6)
        | ~ m1_subset_1(X0,sK6) )
    | ~ spl10_16 ),
    inference(resolution,[],[f136,f65])).

fof(f136,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f331,plain,
    ( spl10_20
    | ~ spl10_45
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f329,f164,f223,f144])).

fof(f223,plain,
    ( spl10_45
  <=> ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl10_30 ),
    inference(resolution,[],[f327,f69])).

fof(f327,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f165,f55])).

fof(f55,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f165,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f164])).

fof(f297,plain,(
    ~ spl10_42 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl10_42 ),
    inference(subsumption_resolution,[],[f59,f292])).

fof(f292,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_42 ),
    inference(resolution,[],[f291,f67])).

fof(f291,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_42 ),
    inference(forward_demodulation,[],[f290,f96])).

fof(f290,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(o_0_0_xboole_0,sK5,sK6,sK7))
    | ~ spl10_42 ),
    inference(backward_demodulation,[],[f283,f57])).

fof(f283,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl10_42 ),
    inference(resolution,[],[f191,f83])).

fof(f191,plain,
    ( v1_xboole_0(sK4)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f190])).

fof(f253,plain,
    ( spl10_19
    | ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl10_19
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f59,f249])).

fof(f249,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_19
    | ~ spl10_28 ),
    inference(backward_demodulation,[],[f162,f139])).

fof(f139,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f138])).

fof(f162,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f161])).

fof(f244,plain,(
    spl10_45 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f59,f224])).

fof(f224,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f223])).

fof(f227,plain,
    ( spl10_15
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f59,f217])).

fof(f217,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_15
    | ~ spl10_26 ),
    inference(backward_demodulation,[],[f159,f130])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f159,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f158])).

fof(f199,plain,
    ( spl10_11
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f59,f195])).

fof(f195,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(backward_demodulation,[],[f156,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f156,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f155])).

fof(f113,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f58,f111,f108,f105,f102])).

fof(f58,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------

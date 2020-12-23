%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t76_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 613 expanded)
%              Number of leaves         :   53 ( 259 expanded)
%              Depth                    :   11
%              Number of atoms          :  689 (2712 expanded)
%              Number of equality atoms :  208 ( 484 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f620,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f168,f194,f203,f236,f266,f294,f305,f308,f385,f403,f426,f448,f463,f496,f511,f514,f524,f542,f543,f544,f546,f551,f561,f570,f587,f592,f594,f599,f604,f611,f619])).

fof(f619,plain,
    ( ~ spl8_77
    | spl8_80
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f615,f577,f617,f582])).

fof(f582,plain,
    ( spl8_77
  <=> ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f617,plain,
    ( spl8_80
  <=> m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f577,plain,
    ( spl8_74
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f615,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_74 ),
    inference(superposition,[],[f71,f578])).

fof(f578,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f577])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_k7_mcart_1)).

fof(f611,plain,
    ( spl8_74
    | spl8_58
    | spl8_56
    | spl8_54
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f605,f148,f338,f341,f344,f577])).

fof(f344,plain,
    ( spl8_58
  <=> o_0_0_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f341,plain,
    ( spl8_56
  <=> o_0_0_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f338,plain,
    ( spl8_54
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f148,plain,
    ( spl8_28
  <=> ! [X7,X8,X6] :
        ( k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(X6,X7,X8,sK6)
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | o_0_0_xboole_0 = X8
        | ~ m1_subset_1(sK6,k3_zfmisc_1(X6,X7,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f605,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_28 ),
    inference(resolution,[],[f152,f149])).

fof(f149,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK6,k3_zfmisc_1(X6,X7,X8))
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | o_0_0_xboole_0 = X8
        | k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(X6,X7,X8,sK6) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f148])).

fof(f152,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t1_subset)).

fof(f53,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f25,f43,f42,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
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
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK4)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
              & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X2)) )
     => ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK5)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK5))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK6),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK6),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK6),X3) )
        & r2_hidden(sK6,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t76_mcart_1)).

fof(f604,plain,
    ( ~ spl8_81
    | spl8_46
    | spl8_5 ),
    inference(avatar_split_clause,[],[f600,f97,f287,f602])).

fof(f602,plain,
    ( spl8_81
  <=> ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f287,plain,
    ( spl8_46
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f97,plain,
    ( spl8_5
  <=> ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f600,plain,
    ( v1_xboole_0(sK5)
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ spl8_5 ),
    inference(resolution,[],[f98,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t2_subset)).

fof(f98,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f599,plain,
    ( ~ spl8_79
    | spl8_40
    | spl8_3 ),
    inference(avatar_split_clause,[],[f595,f94,f211,f597])).

fof(f597,plain,
    ( spl8_79
  <=> ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f211,plain,
    ( spl8_40
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f94,plain,
    ( spl8_3
  <=> ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f595,plain,
    ( v1_xboole_0(sK4)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ spl8_3 ),
    inference(resolution,[],[f95,f61])).

fof(f95,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f594,plain,(
    spl8_77 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl8_77 ),
    inference(subsumption_resolution,[],[f152,f583])).

fof(f583,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f582])).

fof(f592,plain,
    ( ~ spl8_77
    | spl8_78
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f588,f568,f590,f582])).

fof(f590,plain,
    ( spl8_78
  <=> m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f568,plain,
    ( spl8_72
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f588,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_72 ),
    inference(superposition,[],[f70,f569])).

fof(f569,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f568])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_k6_mcart_1)).

fof(f587,plain,
    ( ~ spl8_77
    | spl8_30
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f580,f491,f585,f582])).

fof(f585,plain,
    ( spl8_30
  <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f491,plain,
    ( spl8_70
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f580,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_70 ),
    inference(superposition,[],[f72,f492])).

fof(f492,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f491])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_k5_mcart_1)).

fof(f570,plain,
    ( spl8_72
    | spl8_58
    | spl8_56
    | spl8_54
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f562,f144,f338,f341,f344,f568])).

fof(f144,plain,
    ( spl8_26
  <=> ! [X3,X5,X4] :
        ( k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(X3,X4,X5,sK6)
        | o_0_0_xboole_0 = X3
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | ~ m1_subset_1(sK6,k3_zfmisc_1(X3,X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f562,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_26 ),
    inference(resolution,[],[f145,f152])).

fof(f145,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK6,k3_zfmisc_1(X3,X4,X5))
        | o_0_0_xboole_0 = X3
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(X3,X4,X5,sK6) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f144])).

fof(f561,plain,
    ( spl8_70
    | spl8_58
    | spl8_56
    | spl8_54
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f556,f140,f338,f341,f344,f491])).

fof(f140,plain,
    ( spl8_24
  <=> ! [X1,X0,X2] :
        ( k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(X0,X1,X2,sK6)
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | ~ m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f556,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl8_24 ),
    inference(resolution,[],[f141,f152])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2))
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(X0,X1,X2,sK6) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f140])).

fof(f551,plain,(
    ~ spl8_44 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl8_44 ),
    inference(resolution,[],[f285,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',existence_m1_subset_1)).

fof(f285,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK5)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl8_44
  <=> ! [X0] : ~ m1_subset_1(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f546,plain,
    ( ~ spl8_31
    | spl8_32
    | spl8_1 ),
    inference(avatar_split_clause,[],[f545,f91,f159,f156])).

fof(f156,plain,
    ( spl8_31
  <=> ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f159,plain,
    ( spl8_32
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f91,plain,
    ( spl8_1
  <=> ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f545,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ spl8_1 ),
    inference(resolution,[],[f92,f61])).

fof(f92,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f544,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | spl8_28 ),
    inference(avatar_split_clause,[],[f541,f148,f137,f134,f131])).

fof(f131,plain,
    ( spl8_18
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f134,plain,
    ( spl8_20
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f137,plain,
    ( spl8_22
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f541,plain,(
    ! [X6,X8,X7] :
      ( k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(X6,X7,X8,sK6)
      | ~ m1_subset_1(sK6,k3_zfmisc_1(X6,X7,X8))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X8
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6 ) ),
    inference(resolution,[],[f52,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | k7_mcart_1(X0,X1,X2,X7) = k7_mcart_1(X3,X4,X5,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
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
    inference(definition_unfolding,[],[f75,f56,f56,f56,f56,f56,f56])).

fof(f56,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',d2_xboole_0)).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t75_mcart_1)).

fof(f52,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f543,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | spl8_26 ),
    inference(avatar_split_clause,[],[f540,f144,f137,f134,f131])).

fof(f540,plain,(
    ! [X4,X5,X3] :
      ( k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(X3,X4,X5,sK6)
      | ~ m1_subset_1(sK6,k3_zfmisc_1(X3,X4,X5))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3 ) ),
    inference(resolution,[],[f52,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | k6_mcart_1(X0,X1,X2,X7) = k6_mcart_1(X3,X4,X5,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(definition_unfolding,[],[f74,f56,f56,f56,f56,f56,f56])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f542,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | spl8_24 ),
    inference(avatar_split_clause,[],[f539,f140,f137,f134,f131])).

fof(f539,plain,(
    ! [X2,X0,X1] :
      ( k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(X0,X1,X2,sK6)
      | ~ m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f52,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | k5_mcart_1(X0,X1,X2,X7) = k5_mcart_1(X3,X4,X5,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
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
    inference(definition_unfolding,[],[f73,f56,f56,f56,f56,f56,f56])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f524,plain,
    ( spl8_44
    | spl8_46
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f523,f121,f287,f284])).

fof(f121,plain,
    ( spl8_14
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f523,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK5)
        | ~ m1_subset_1(X0,sK5) )
    | ~ spl8_14 ),
    inference(resolution,[],[f122,f61])).

fof(f122,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f514,plain,
    ( spl8_6
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f512,f106,f103])).

fof(f103,plain,
    ( spl8_6
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f106,plain,
    ( spl8_9
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f512,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f49,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t5_subset)).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f511,plain,(
    ~ spl8_42 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl8_42 ),
    inference(resolution,[],[f225,f58])).

fof(f225,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK3)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl8_42
  <=> ! [X0] : ~ m1_subset_1(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f496,plain,
    ( spl8_42
    | spl8_32
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f495,f103,f159,f224])).

fof(f495,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f61])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f463,plain,(
    ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f55,f459])).

fof(f459,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_46 ),
    inference(resolution,[],[f458,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t7_boole)).

fof(f458,plain,
    ( r2_hidden(sK6,o_0_0_xboole_0)
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f457,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_zfmisc_1(X0,X1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f68,f56,f56])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t35_mcart_1)).

fof(f457,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,o_0_0_xboole_0))
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f53,f359])).

fof(f359,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl8_46 ),
    inference(resolution,[],[f288,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t6_boole)).

fof(f288,plain,
    ( v1_xboole_0(sK5)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f287])).

fof(f55,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_o_0_0_xboole_0)).

fof(f448,plain,(
    ~ spl8_40 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f55,f440])).

fof(f440,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f436,f85])).

fof(f85,plain,(
    ! [X2,X0] : k3_zfmisc_1(X0,o_0_0_xboole_0,X2) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f67,f56,f56])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f436,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(sK3,o_0_0_xboole_0,sK5))
    | ~ spl8_40 ),
    inference(backward_demodulation,[],[f328,f151])).

fof(f151,plain,(
    ~ v1_xboole_0(k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(resolution,[],[f53,f63])).

fof(f328,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl8_40 ),
    inference(resolution,[],[f212,f76])).

fof(f212,plain,
    ( v1_xboole_0(sK4)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f211])).

fof(f426,plain,(
    ~ spl8_58 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f55,f419])).

fof(f419,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_58 ),
    inference(forward_demodulation,[],[f416,f84])).

fof(f416,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(sK3,sK4,o_0_0_xboole_0))
    | ~ spl8_58 ),
    inference(backward_demodulation,[],[f345,f151])).

fof(f345,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f344])).

fof(f403,plain,(
    ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f55,f397])).

fof(f397,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_56 ),
    inference(resolution,[],[f396,f63])).

fof(f396,plain,
    ( r2_hidden(sK6,o_0_0_xboole_0)
    | ~ spl8_56 ),
    inference(forward_demodulation,[],[f395,f85])).

fof(f395,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(sK3,o_0_0_xboole_0,sK5))
    | ~ spl8_56 ),
    inference(forward_demodulation,[],[f53,f342])).

fof(f342,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f341])).

fof(f385,plain,(
    ~ spl8_54 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f55,f376])).

fof(f376,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_54 ),
    inference(forward_demodulation,[],[f372,f86])).

fof(f86,plain,(
    ! [X2,X1] : k3_zfmisc_1(o_0_0_xboole_0,X1,X2) = o_0_0_xboole_0 ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f66,f56,f56])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f372,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(o_0_0_xboole_0,sK4,sK5))
    | ~ spl8_54 ),
    inference(backward_demodulation,[],[f339,f151])).

fof(f339,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f338])).

fof(f308,plain,
    ( spl8_10
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f306,f115,f112])).

fof(f112,plain,
    ( spl8_10
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f115,plain,
    ( spl8_13
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f306,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f50,f69])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f305,plain,(
    ~ spl8_38 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl8_38 ),
    inference(resolution,[],[f209,f58])).

fof(f209,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_38
  <=> ! [X0] : ~ m1_subset_1(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f294,plain,
    ( spl8_38
    | spl8_40
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f293,f112,f211,f208])).

fof(f293,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4)
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl8_10 ),
    inference(resolution,[],[f113,f61])).

fof(f113,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f266,plain,(
    ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f55,f260])).

fof(f260,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_32 ),
    inference(resolution,[],[f259,f63])).

fof(f259,plain,
    ( r2_hidden(sK6,o_0_0_xboole_0)
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f258,f86])).

fof(f258,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(o_0_0_xboole_0,sK4,sK5))
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f246,f53])).

fof(f246,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl8_32 ),
    inference(resolution,[],[f160,f76])).

fof(f160,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f159])).

fof(f236,plain,
    ( spl8_14
    | ~ spl8_35
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f234,f137,f190,f121])).

fof(f190,plain,
    ( spl8_35
  <=> ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | ~ r2_hidden(X0,sK5) )
    | ~ spl8_22 ),
    inference(resolution,[],[f232,f69])).

fof(f232,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f138,f51])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f138,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f203,plain,(
    spl8_35 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f55,f191])).

fof(f191,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f190])).

fof(f194,plain,
    ( spl8_13
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f55,f184])).

fof(f184,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f135,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f135,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f134])).

fof(f168,plain,
    ( spl8_9
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f55,f164])).

fof(f164,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f132,f107])).

fof(f107,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f132,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f99,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f54,f97,f94,f91])).

fof(f54,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------

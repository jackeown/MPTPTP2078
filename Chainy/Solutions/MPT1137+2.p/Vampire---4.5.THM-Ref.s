%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1137+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 6.14s
% Output     : Refutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 315 expanded)
%              Number of leaves         :   13 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 (1998 expanded)
%              Number of equality atoms :   25 ( 278 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10516,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10515,f5426])).

fof(f5426,plain,(
    v1_relat_1(u1_orders_2(sK35)) ),
    inference(resolution,[],[f5032,f3549])).

fof(f3549,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1950])).

fof(f1950,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f5032,plain,(
    m1_subset_1(u1_orders_2(sK35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK35),u1_struct_0(sK35)))) ),
    inference(resolution,[],[f3475,f3602])).

fof(f3602,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f1993])).

fof(f1993,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1866])).

fof(f1866,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3475,plain,(
    l1_orders_2(sK35) ),
    inference(cnf_transformation,[],[f2793])).

fof(f2793,plain,
    ( sK36 != sK37
    & r1_orders_2(sK35,sK37,sK36)
    & r1_orders_2(sK35,sK36,sK37)
    & m1_subset_1(sK37,u1_struct_0(sK35))
    & m1_subset_1(sK36,u1_struct_0(sK35))
    & l1_orders_2(sK35)
    & v5_orders_2(sK35) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f1897,f2792,f2791,f2790])).

fof(f2790,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK35,X2,X1)
              & r1_orders_2(sK35,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK35)) )
          & m1_subset_1(X1,u1_struct_0(sK35)) )
      & l1_orders_2(sK35)
      & v5_orders_2(sK35) ) ),
    introduced(choice_axiom,[])).

fof(f2791,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_orders_2(sK35,X2,X1)
            & r1_orders_2(sK35,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK35)) )
        & m1_subset_1(X1,u1_struct_0(sK35)) )
   => ( ? [X2] :
          ( sK36 != X2
          & r1_orders_2(sK35,X2,sK36)
          & r1_orders_2(sK35,sK36,X2)
          & m1_subset_1(X2,u1_struct_0(sK35)) )
      & m1_subset_1(sK36,u1_struct_0(sK35)) ) ),
    introduced(choice_axiom,[])).

fof(f2792,plain,
    ( ? [X2] :
        ( sK36 != X2
        & r1_orders_2(sK35,X2,sK36)
        & r1_orders_2(sK35,sK36,X2)
        & m1_subset_1(X2,u1_struct_0(sK35)) )
   => ( sK36 != sK37
      & r1_orders_2(sK35,sK37,sK36)
      & r1_orders_2(sK35,sK36,sK37)
      & m1_subset_1(sK37,u1_struct_0(sK35)) ) ),
    introduced(choice_axiom,[])).

fof(f1897,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f1896])).

fof(f1896,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1873])).

fof(f1873,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1872])).

fof(f1872,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f10515,plain,(
    ~ v1_relat_1(u1_orders_2(sK35)) ),
    inference(subsumption_resolution,[],[f10514,f5623])).

fof(f5623,plain,(
    r2_hidden(sK36,u1_struct_0(sK35)) ),
    inference(resolution,[],[f5496,f5043])).

fof(f5043,plain,
    ( v1_xboole_0(u1_struct_0(sK35))
    | r2_hidden(sK36,u1_struct_0(sK35)) ),
    inference(resolution,[],[f3476,f3571])).

fof(f3571,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2832])).

fof(f2832,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1970])).

fof(f1970,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f3476,plain,(
    m1_subset_1(sK36,u1_struct_0(sK35)) ),
    inference(cnf_transformation,[],[f2793])).

fof(f5496,plain,(
    ~ v1_xboole_0(u1_struct_0(sK35)) ),
    inference(subsumption_resolution,[],[f5428,f5115])).

fof(f5115,plain,(
    ~ v1_xboole_0(u1_orders_2(sK35)) ),
    inference(resolution,[],[f5056,f4057])).

fof(f4057,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2253])).

fof(f2253,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f5056,plain,(
    r2_hidden(k4_tarski(sK36,sK37),u1_orders_2(sK35)) ),
    inference(subsumption_resolution,[],[f5055,f3475])).

fof(f5055,plain,
    ( r2_hidden(k4_tarski(sK36,sK37),u1_orders_2(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(subsumption_resolution,[],[f5054,f3476])).

fof(f5054,plain,
    ( r2_hidden(k4_tarski(sK36,sK37),u1_orders_2(sK35))
    | ~ m1_subset_1(sK36,u1_struct_0(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(subsumption_resolution,[],[f5053,f3477])).

fof(f3477,plain,(
    m1_subset_1(sK37,u1_struct_0(sK35)) ),
    inference(cnf_transformation,[],[f2793])).

fof(f5053,plain,
    ( r2_hidden(k4_tarski(sK36,sK37),u1_orders_2(sK35))
    | ~ m1_subset_1(sK37,u1_struct_0(sK35))
    | ~ m1_subset_1(sK36,u1_struct_0(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(resolution,[],[f3478,f3517])).

fof(f3517,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2819])).

fof(f2819,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f1921])).

fof(f1921,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1863])).

fof(f1863,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f3478,plain,(
    r1_orders_2(sK35,sK36,sK37) ),
    inference(cnf_transformation,[],[f2793])).

fof(f5428,plain,
    ( v1_xboole_0(u1_orders_2(sK35))
    | ~ v1_xboole_0(u1_struct_0(sK35)) ),
    inference(resolution,[],[f5032,f3569])).

fof(f3569,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1968])).

fof(f1968,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f1213,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f10514,plain,
    ( ~ r2_hidden(sK36,u1_struct_0(sK35))
    | ~ v1_relat_1(u1_orders_2(sK35)) ),
    inference(subsumption_resolution,[],[f10513,f5622])).

fof(f5622,plain,(
    r2_hidden(sK37,u1_struct_0(sK35)) ),
    inference(resolution,[],[f5496,f5049])).

fof(f5049,plain,
    ( v1_xboole_0(u1_struct_0(sK35))
    | r2_hidden(sK37,u1_struct_0(sK35)) ),
    inference(resolution,[],[f3477,f3571])).

fof(f10513,plain,
    ( ~ r2_hidden(sK37,u1_struct_0(sK35))
    | ~ r2_hidden(sK36,u1_struct_0(sK35))
    | ~ v1_relat_1(u1_orders_2(sK35)) ),
    inference(resolution,[],[f5140,f5030])).

fof(f5030,plain,(
    r4_relat_2(u1_orders_2(sK35),u1_struct_0(sK35)) ),
    inference(subsumption_resolution,[],[f5029,f3475])).

fof(f5029,plain,
    ( r4_relat_2(u1_orders_2(sK35),u1_struct_0(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(resolution,[],[f3474,f3604])).

fof(f3604,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2844])).

fof(f2844,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f1995])).

fof(f1995,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1862])).

fof(f1862,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

fof(f3474,plain,(
    v5_orders_2(sK35) ),
    inference(cnf_transformation,[],[f2793])).

fof(f5140,plain,(
    ! [X9] :
      ( ~ r4_relat_2(u1_orders_2(sK35),X9)
      | ~ r2_hidden(sK37,X9)
      | ~ r2_hidden(sK36,X9)
      | ~ v1_relat_1(u1_orders_2(sK35)) ) ),
    inference(subsumption_resolution,[],[f5139,f5060])).

fof(f5060,plain,(
    r2_hidden(k4_tarski(sK37,sK36),u1_orders_2(sK35)) ),
    inference(subsumption_resolution,[],[f5059,f3475])).

fof(f5059,plain,
    ( r2_hidden(k4_tarski(sK37,sK36),u1_orders_2(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(subsumption_resolution,[],[f5058,f3477])).

fof(f5058,plain,
    ( r2_hidden(k4_tarski(sK37,sK36),u1_orders_2(sK35))
    | ~ m1_subset_1(sK37,u1_struct_0(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(subsumption_resolution,[],[f5057,f3476])).

fof(f5057,plain,
    ( r2_hidden(k4_tarski(sK37,sK36),u1_orders_2(sK35))
    | ~ m1_subset_1(sK36,u1_struct_0(sK35))
    | ~ m1_subset_1(sK37,u1_struct_0(sK35))
    | ~ l1_orders_2(sK35) ),
    inference(resolution,[],[f3479,f3517])).

fof(f3479,plain,(
    r1_orders_2(sK35,sK37,sK36) ),
    inference(cnf_transformation,[],[f2793])).

fof(f5139,plain,(
    ! [X9] :
      ( ~ r2_hidden(k4_tarski(sK37,sK36),u1_orders_2(sK35))
      | ~ r2_hidden(sK36,X9)
      | ~ r2_hidden(sK37,X9)
      | ~ r4_relat_2(u1_orders_2(sK35),X9)
      | ~ v1_relat_1(u1_orders_2(sK35)) ) ),
    inference(subsumption_resolution,[],[f5085,f3480])).

fof(f3480,plain,(
    sK36 != sK37 ),
    inference(cnf_transformation,[],[f2793])).

fof(f5085,plain,(
    ! [X9] :
      ( sK36 = sK37
      | ~ r2_hidden(k4_tarski(sK37,sK36),u1_orders_2(sK35))
      | ~ r2_hidden(sK36,X9)
      | ~ r2_hidden(sK37,X9)
      | ~ r4_relat_2(u1_orders_2(sK35),X9)
      | ~ v1_relat_1(u1_orders_2(sK35)) ) ),
    inference(resolution,[],[f5056,f4842])).

fof(f4842,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3472])).

fof(f3472,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ( sK282(X0,X1) != sK283(X0,X1)
              & r2_hidden(k4_tarski(sK283(X0,X1),sK282(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK282(X0,X1),sK283(X0,X1)),X0)
              & r2_hidden(sK283(X0,X1),X1)
              & r2_hidden(sK282(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK282,sK283])],[f3470,f3471])).

fof(f3471,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK282(X0,X1) != sK283(X0,X1)
        & r2_hidden(k4_tarski(sK283(X0,X1),sK282(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK282(X0,X1),sK283(X0,X1)),X0)
        & r2_hidden(sK283(X0,X1),X1)
        & r2_hidden(sK282(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3470,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f3469])).

fof(f3469,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( X2 = X3
                | ~ r2_hidden(k4_tarski(X3,X2),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2729])).

fof(f2729,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2728])).

fof(f2728,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1422])).

fof(f1422,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).
%------------------------------------------------------------------------------

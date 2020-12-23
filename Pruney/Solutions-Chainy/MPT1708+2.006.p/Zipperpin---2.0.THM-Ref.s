%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Esa5iWdkD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:13 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 346 expanded)
%              Number of leaves         :   40 ( 111 expanded)
%              Depth                    :   36
%              Number of atoms          : 1893 (7576 expanded)
%              Number of equality atoms :   59 ( 308 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t17_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                   => ( ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                      & ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ~ ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                     => ( ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                        & ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X24 @ X31 )
      | ( X31
       != ( k4_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X24 @ ( k4_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X17 != X18 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X16: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X16 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ( r1_tsep_1 @ X43 @ X45 )
      | ( v2_struct_0 @ X46 )
      | ~ ( v1_pre_topc @ X46 )
      | ~ ( m1_pre_topc @ X46 @ X44 )
      | ( X46
       != ( k2_tsep_1 @ X44 @ X43 @ X45 ) )
      | ( ( u1_struct_0 @ X46 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_pre_topc @ X45 @ X44 )
      | ( v2_struct_0 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ( v2_struct_0 @ X45 )
      | ~ ( m1_pre_topc @ X45 @ X44 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X44 @ X43 @ X45 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X44 @ X43 @ X45 ) @ X44 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X44 @ X43 @ X45 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X44 @ X43 @ X45 ) )
      | ( r1_tsep_1 @ X43 @ X45 )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('50',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X52 ) )
      | ( m1_pre_topc @ X50 @ X52 )
      | ~ ( m1_pre_topc @ X52 @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ~ ( l1_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('64',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( l1_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) )
      | ( X53 != sk_D )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ sk_C ) )
      | ( X54 != sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ! [X54: $i] :
        ( ( X54 != sk_D )
        | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X54: $i] :
        ( ( X54 != sk_D )
        | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
   <= ! [X54: $i] :
        ( ( X54 != sk_D )
        | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( l1_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
   <= ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ~ ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X54: $i] :
        ( ( X54 != sk_D )
        | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ sk_C ) ) )
    | ! [X53: $i] :
        ( ( X53 != sk_D )
        | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('118',plain,(
    ! [X54: $i] :
      ( ( X54 != sk_D )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['79','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['76','119'])).

thf('121',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['0','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Esa5iWdkD
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.93/2.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.16  % Solved by: fo/fo7.sh
% 1.93/2.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.16  % done 1036 iterations in 1.705s
% 1.93/2.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.16  % SZS output start Refutation
% 1.93/2.16  thf(sk_D_type, type, sk_D: $i).
% 1.93/2.16  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.93/2.16  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.93/2.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 1.93/2.16  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.93/2.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.93/2.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.93/2.16  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.93/2.16  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.16  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.93/2.16  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 1.93/2.16  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.93/2.16  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.93/2.16  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.93/2.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.93/2.16  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.93/2.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.93/2.16  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.16  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.93/2.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.93/2.16  thf(t17_tmap_1, conjecture,
% 1.93/2.16    (![A:$i]:
% 1.93/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.16       ( ![B:$i]:
% 1.93/2.16         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.16           ( ![C:$i]:
% 1.93/2.16             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.16               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.93/2.16                 ( ![D:$i]:
% 1.93/2.16                   ( ( m1_subset_1 @
% 1.93/2.16                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.93/2.16                     ( ( ?[E:$i]:
% 1.93/2.16                         ( ( ( E ) = ( D ) ) & 
% 1.93/2.16                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.93/2.16                       ( ?[E:$i]:
% 1.93/2.16                         ( ( ( E ) = ( D ) ) & 
% 1.93/2.16                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.16  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.16    (~( ![A:$i]:
% 1.93/2.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.93/2.16            ( l1_pre_topc @ A ) ) =>
% 1.93/2.16          ( ![B:$i]:
% 1.93/2.16            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.16              ( ![C:$i]:
% 1.93/2.16                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.16                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.93/2.16                    ( ![D:$i]:
% 1.93/2.16                      ( ( m1_subset_1 @
% 1.93/2.16                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.93/2.16                        ( ( ?[E:$i]:
% 1.93/2.16                            ( ( ( E ) = ( D ) ) & 
% 1.93/2.16                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.93/2.16                          ( ?[E:$i]:
% 1.93/2.16                            ( ( ( E ) = ( D ) ) & 
% 1.93/2.16                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.93/2.16    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 1.93/2.16  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf(dt_k2_tsep_1, axiom,
% 1.93/2.16    (![A:$i,B:$i,C:$i]:
% 1.93/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.93/2.16         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.93/2.16         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.16       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 1.93/2.16         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 1.93/2.16         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.93/2.16  thf('3', plain,
% 1.93/2.16      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X47 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X47)
% 1.93/2.16          | ~ (l1_pre_topc @ X48)
% 1.93/2.16          | (v2_struct_0 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X49)
% 1.93/2.16          | ~ (m1_pre_topc @ X49 @ X48)
% 1.93/2.16          | (m1_pre_topc @ (k2_tsep_1 @ X48 @ X47 @ X49) @ X48))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.16  thf('4', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.93/2.16          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ X0)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('sup-', [status(thm)], ['2', '3'])).
% 1.93/2.16  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('6', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.93/2.16          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ X0)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['4', '5'])).
% 1.93/2.16  thf('7', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['1', '6'])).
% 1.93/2.16  thf(t70_enumset1, axiom,
% 1.93/2.16    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.93/2.16  thf('8', plain,
% 1.93/2.16      (![X2 : $i, X3 : $i]:
% 1.93/2.16         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.93/2.16      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.93/2.16  thf(t71_enumset1, axiom,
% 1.93/2.16    (![A:$i,B:$i,C:$i]:
% 1.93/2.16     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.93/2.16  thf('9', plain,
% 1.93/2.16      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.93/2.16         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.93/2.16      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.93/2.16  thf(t72_enumset1, axiom,
% 1.93/2.16    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.16     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.93/2.16  thf('10', plain,
% 1.93/2.16      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.16         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 1.93/2.16           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 1.93/2.16      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.93/2.16  thf(t73_enumset1, axiom,
% 1.93/2.16    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.93/2.16     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.93/2.16       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.93/2.16  thf('11', plain,
% 1.93/2.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.93/2.16         ((k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15)
% 1.93/2.16           = (k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 1.93/2.16      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.93/2.16  thf(d4_enumset1, axiom,
% 1.93/2.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.93/2.16     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.93/2.16       ( ![H:$i]:
% 1.93/2.16         ( ( r2_hidden @ H @ G ) <=>
% 1.93/2.16           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 1.93/2.16                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 1.93/2.16  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 1.93/2.16  thf(zf_stmt_2, axiom,
% 1.93/2.16    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.93/2.16     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 1.93/2.16       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 1.93/2.16         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 1.93/2.16  thf(zf_stmt_3, axiom,
% 1.93/2.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.93/2.16     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.93/2.16       ( ![H:$i]:
% 1.93/2.16         ( ( r2_hidden @ H @ G ) <=>
% 1.93/2.16           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.93/2.16  thf('12', plain,
% 1.93/2.16      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 1.93/2.16         X31 : $i]:
% 1.93/2.16         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 1.93/2.16          | (r2_hidden @ X24 @ X31)
% 1.93/2.16          | ((X31) != (k4_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26 @ X25)))),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.93/2.16  thf('13', plain,
% 1.93/2.16      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.93/2.16         ((r2_hidden @ X24 @ (k4_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26 @ X25))
% 1.93/2.16          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 1.93/2.16      inference('simplify', [status(thm)], ['12'])).
% 1.93/2.16  thf('14', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.93/2.16         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.93/2.16          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 1.93/2.16      inference('sup+', [status(thm)], ['11', '13'])).
% 1.93/2.16  thf('15', plain,
% 1.93/2.16      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.93/2.16         (((X17) != (X18))
% 1.93/2.16          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X16))),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.16  thf('16', plain,
% 1.93/2.16      (![X16 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.93/2.16         ~ (zip_tseitin_0 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X16)),
% 1.93/2.16      inference('simplify', [status(thm)], ['15'])).
% 1.93/2.16  thf('17', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.93/2.16         (r2_hidden @ X4 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 1.93/2.16      inference('sup-', [status(thm)], ['14', '16'])).
% 1.93/2.16  thf('18', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.93/2.16         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.93/2.16      inference('sup+', [status(thm)], ['10', '17'])).
% 1.93/2.16  thf('19', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.16         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.93/2.16      inference('sup+', [status(thm)], ['9', '18'])).
% 1.93/2.16  thf('20', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.93/2.16      inference('sup+', [status(thm)], ['8', '19'])).
% 1.93/2.16  thf(t4_setfam_1, axiom,
% 1.93/2.16    (![A:$i,B:$i]:
% 1.93/2.16     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.93/2.16  thf('21', plain,
% 1.93/2.16      (![X36 : $i, X37 : $i]:
% 1.93/2.16         ((r1_tarski @ (k1_setfam_1 @ X36) @ X37) | ~ (r2_hidden @ X37 @ X36))),
% 1.93/2.16      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.93/2.16  thf('22', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i]:
% 1.93/2.16         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.93/2.16      inference('sup-', [status(thm)], ['20', '21'])).
% 1.93/2.16  thf(t12_setfam_1, axiom,
% 1.93/2.16    (![A:$i,B:$i]:
% 1.93/2.16     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.93/2.16  thf('23', plain,
% 1.93/2.16      (![X34 : $i, X35 : $i]:
% 1.93/2.16         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 1.93/2.16      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.93/2.16  thf('24', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.93/2.16      inference('demod', [status(thm)], ['22', '23'])).
% 1.93/2.16  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('27', plain,
% 1.93/2.16      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X47 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X47)
% 1.93/2.16          | ~ (l1_pre_topc @ X48)
% 1.93/2.16          | (v2_struct_0 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X49)
% 1.93/2.16          | ~ (m1_pre_topc @ X49 @ X48)
% 1.93/2.16          | (v1_pre_topc @ (k2_tsep_1 @ X48 @ X47 @ X49)))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.16  thf('28', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 1.93/2.16          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ X0)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('sup-', [status(thm)], ['26', '27'])).
% 1.93/2.16  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('30', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 1.93/2.16          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ X0)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['28', '29'])).
% 1.93/2.16  thf('31', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.16      inference('sup-', [status(thm)], ['25', '30'])).
% 1.93/2.16  thf('32', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['1', '6'])).
% 1.93/2.16  thf(d5_tsep_1, axiom,
% 1.93/2.16    (![A:$i]:
% 1.93/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.16       ( ![B:$i]:
% 1.93/2.16         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.16           ( ![C:$i]:
% 1.93/2.16             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.16               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.93/2.16                 ( ![D:$i]:
% 1.93/2.16                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.93/2.16                       ( m1_pre_topc @ D @ A ) ) =>
% 1.93/2.16                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 1.93/2.16                       ( ( u1_struct_0 @ D ) =
% 1.93/2.16                         ( k3_xboole_0 @
% 1.93/2.16                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.16  thf('33', plain,
% 1.93/2.16      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.93/2.16         ((v2_struct_0 @ X43)
% 1.93/2.16          | ~ (m1_pre_topc @ X43 @ X44)
% 1.93/2.16          | (r1_tsep_1 @ X43 @ X45)
% 1.93/2.16          | (v2_struct_0 @ X46)
% 1.93/2.16          | ~ (v1_pre_topc @ X46)
% 1.93/2.16          | ~ (m1_pre_topc @ X46 @ X44)
% 1.93/2.16          | ((X46) != (k2_tsep_1 @ X44 @ X43 @ X45))
% 1.93/2.16          | ((u1_struct_0 @ X46)
% 1.93/2.16              = (k3_xboole_0 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X45)))
% 1.93/2.16          | ~ (m1_pre_topc @ X45 @ X44)
% 1.93/2.16          | (v2_struct_0 @ X45)
% 1.93/2.16          | ~ (l1_pre_topc @ X44)
% 1.93/2.16          | (v2_struct_0 @ X44))),
% 1.93/2.16      inference('cnf', [status(esa)], [d5_tsep_1])).
% 1.93/2.16  thf('34', plain,
% 1.93/2.16      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.93/2.16         ((v2_struct_0 @ X44)
% 1.93/2.16          | ~ (l1_pre_topc @ X44)
% 1.93/2.16          | (v2_struct_0 @ X45)
% 1.93/2.16          | ~ (m1_pre_topc @ X45 @ X44)
% 1.93/2.16          | ((u1_struct_0 @ (k2_tsep_1 @ X44 @ X43 @ X45))
% 1.93/2.16              = (k3_xboole_0 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X45)))
% 1.93/2.16          | ~ (m1_pre_topc @ (k2_tsep_1 @ X44 @ X43 @ X45) @ X44)
% 1.93/2.16          | ~ (v1_pre_topc @ (k2_tsep_1 @ X44 @ X43 @ X45))
% 1.93/2.16          | (v2_struct_0 @ (k2_tsep_1 @ X44 @ X43 @ X45))
% 1.93/2.16          | (r1_tsep_1 @ X43 @ X45)
% 1.93/2.16          | ~ (m1_pre_topc @ X43 @ X44)
% 1.93/2.16          | (v2_struct_0 @ X43))),
% 1.93/2.16      inference('simplify', [status(thm)], ['33'])).
% 1.93/2.16  thf('35', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['32', '34'])).
% 1.93/2.16  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('39', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A))),
% 1.93/2.16      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.93/2.16  thf('40', plain,
% 1.93/2.16      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['39'])).
% 1.93/2.16  thf('41', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.93/2.16      inference('sup-', [status(thm)], ['31', '40'])).
% 1.93/2.16  thf('42', plain,
% 1.93/2.16      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['41'])).
% 1.93/2.16  thf('43', plain,
% 1.93/2.16      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X47 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X47)
% 1.93/2.16          | ~ (l1_pre_topc @ X48)
% 1.93/2.16          | (v2_struct_0 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X49)
% 1.93/2.16          | ~ (m1_pre_topc @ X49 @ X48)
% 1.93/2.16          | ~ (v2_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49)))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.16  thf('44', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['42', '43'])).
% 1.93/2.16  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('48', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.93/2.16  thf('49', plain,
% 1.93/2.16      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['48'])).
% 1.93/2.16  thf(t4_tsep_1, axiom,
% 1.93/2.16    (![A:$i]:
% 1.93/2.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.16       ( ![B:$i]:
% 1.93/2.16         ( ( m1_pre_topc @ B @ A ) =>
% 1.93/2.16           ( ![C:$i]:
% 1.93/2.16             ( ( m1_pre_topc @ C @ A ) =>
% 1.93/2.16               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.93/2.16                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.93/2.16  thf('50', plain,
% 1.93/2.16      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X50 @ X51)
% 1.93/2.16          | ~ (r1_tarski @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X52))
% 1.93/2.16          | (m1_pre_topc @ X50 @ X52)
% 1.93/2.16          | ~ (m1_pre_topc @ X52 @ X51)
% 1.93/2.16          | ~ (l1_pre_topc @ X51)
% 1.93/2.16          | ~ (v2_pre_topc @ X51))),
% 1.93/2.16      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.93/2.16  thf('51', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i]:
% 1.93/2.16         (~ (r1_tarski @ 
% 1.93/2.16             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 1.93/2.16             (u1_struct_0 @ X0))
% 1.93/2.16          | (v2_struct_0 @ sk_C)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_B)
% 1.93/2.16          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16          | ~ (v2_pre_topc @ X1)
% 1.93/2.16          | ~ (l1_pre_topc @ X1)
% 1.93/2.16          | ~ (m1_pre_topc @ X0 @ X1)
% 1.93/2.16          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.16          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 1.93/2.16      inference('sup-', [status(thm)], ['49', '50'])).
% 1.93/2.16  thf('52', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.16          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.93/2.16          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.93/2.16          | ~ (l1_pre_topc @ X0)
% 1.93/2.16          | ~ (v2_pre_topc @ X0)
% 1.93/2.16          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16          | (v2_struct_0 @ sk_B)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['24', '51'])).
% 1.93/2.16  thf('53', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.16        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['7', '52'])).
% 1.93/2.16  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('57', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 1.93/2.16      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 1.93/2.16  thf('58', plain,
% 1.93/2.16      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['57'])).
% 1.93/2.16  thf('59', plain,
% 1.93/2.16      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf(t55_pre_topc, axiom,
% 1.93/2.16    (![A:$i]:
% 1.93/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.16       ( ![B:$i]:
% 1.93/2.16         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.16           ( ![C:$i]:
% 1.93/2.16             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.16               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.93/2.16  thf('60', plain,
% 1.93/2.16      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.93/2.16         ((v2_struct_0 @ X40)
% 1.93/2.16          | ~ (m1_pre_topc @ X40 @ X41)
% 1.93/2.16          | (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.93/2.16          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 1.93/2.16          | ~ (l1_pre_topc @ X41)
% 1.93/2.16          | (v2_struct_0 @ X41))),
% 1.93/2.16      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.93/2.16  thf('61', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         ((v2_struct_0 @ X0)
% 1.93/2.16          | ~ (l1_pre_topc @ X0)
% 1.93/2.16          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 1.93/2.16          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.16          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.16      inference('sup-', [status(thm)], ['59', '60'])).
% 1.93/2.16  thf('62', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.16        | ~ (l1_pre_topc @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['58', '61'])).
% 1.93/2.16  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf(dt_m1_pre_topc, axiom,
% 1.93/2.16    (![A:$i]:
% 1.93/2.16     ( ( l1_pre_topc @ A ) =>
% 1.93/2.16       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.93/2.16  thf('64', plain,
% 1.93/2.16      (![X38 : $i, X39 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X38 @ X39)
% 1.93/2.16          | (l1_pre_topc @ X38)
% 1.93/2.16          | ~ (l1_pre_topc @ X39))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.16  thf('65', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['63', '64'])).
% 1.93/2.16  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('67', plain, ((l1_pre_topc @ sk_C)),
% 1.93/2.16      inference('demod', [status(thm)], ['65', '66'])).
% 1.93/2.16  thf('68', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('demod', [status(thm)], ['62', '67'])).
% 1.93/2.16  thf('69', plain,
% 1.93/2.16      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['68'])).
% 1.93/2.16  thf('70', plain,
% 1.93/2.16      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X47 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X47)
% 1.93/2.16          | ~ (l1_pre_topc @ X48)
% 1.93/2.16          | (v2_struct_0 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X49)
% 1.93/2.16          | ~ (m1_pre_topc @ X49 @ X48)
% 1.93/2.16          | ~ (v2_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49)))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.16  thf('71', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.16        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['69', '70'])).
% 1.93/2.16  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('75', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 1.93/2.16  thf('76', plain,
% 1.93/2.16      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['75'])).
% 1.93/2.16  thf('77', plain,
% 1.93/2.16      (![X53 : $i, X54 : $i]:
% 1.93/2.16         (~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B))
% 1.93/2.16          | ((X53) != (sk_D))
% 1.93/2.16          | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ sk_C))
% 1.93/2.16          | ((X54) != (sk_D)))),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('78', plain,
% 1.93/2.16      ((![X54 : $i]:
% 1.93/2.16          (((X54) != (sk_D)) | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ sk_C))))
% 1.93/2.16         <= ((![X54 : $i]:
% 1.93/2.16                (((X54) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ sk_C)))))),
% 1.93/2.16      inference('split', [status(esa)], ['77'])).
% 1.93/2.16  thf('79', plain,
% 1.93/2.16      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 1.93/2.16         <= ((![X54 : $i]:
% 1.93/2.16                (((X54) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ sk_C)))))),
% 1.93/2.16      inference('simplify', [status(thm)], ['78'])).
% 1.93/2.16  thf('80', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['1', '6'])).
% 1.93/2.16  thf(t17_xboole_1, axiom,
% 1.93/2.16    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.93/2.16  thf('81', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.93/2.16      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.93/2.16  thf('82', plain,
% 1.93/2.16      (![X0 : $i, X1 : $i]:
% 1.93/2.16         (~ (r1_tarski @ 
% 1.93/2.16             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 1.93/2.16             (u1_struct_0 @ X0))
% 1.93/2.16          | (v2_struct_0 @ sk_C)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_B)
% 1.93/2.16          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16          | ~ (v2_pre_topc @ X1)
% 1.93/2.16          | ~ (l1_pre_topc @ X1)
% 1.93/2.16          | ~ (m1_pre_topc @ X0 @ X1)
% 1.93/2.16          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.16          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 1.93/2.16      inference('sup-', [status(thm)], ['49', '50'])).
% 1.93/2.16  thf('83', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.16          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.93/2.16          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.16          | ~ (l1_pre_topc @ X0)
% 1.93/2.16          | ~ (v2_pre_topc @ X0)
% 1.93/2.16          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16          | (v2_struct_0 @ sk_B)
% 1.93/2.16          | (v2_struct_0 @ sk_A)
% 1.93/2.16          | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['81', '82'])).
% 1.93/2.16  thf('84', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.16        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 1.93/2.16      inference('sup-', [status(thm)], ['80', '83'])).
% 1.93/2.16  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('87', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('88', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 1.93/2.16  thf('89', plain,
% 1.93/2.16      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['88'])).
% 1.93/2.16  thf('90', plain,
% 1.93/2.16      (![X0 : $i]:
% 1.93/2.16         ((v2_struct_0 @ X0)
% 1.93/2.16          | ~ (l1_pre_topc @ X0)
% 1.93/2.16          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 1.93/2.16          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.16          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.16      inference('sup-', [status(thm)], ['59', '60'])).
% 1.93/2.16  thf('91', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.16        | ~ (l1_pre_topc @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('sup-', [status(thm)], ['89', '90'])).
% 1.93/2.16  thf('92', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('93', plain,
% 1.93/2.16      (![X38 : $i, X39 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X38 @ X39)
% 1.93/2.16          | (l1_pre_topc @ X38)
% 1.93/2.16          | ~ (l1_pre_topc @ X39))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.16  thf('94', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.93/2.16      inference('sup-', [status(thm)], ['92', '93'])).
% 1.93/2.16  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.16      inference('demod', [status(thm)], ['94', '95'])).
% 1.93/2.16  thf('97', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.16        | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['91', '96'])).
% 1.93/2.16  thf('98', plain,
% 1.93/2.16      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.16        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['97'])).
% 1.93/2.16  thf('99', plain,
% 1.93/2.16      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.93/2.16         (~ (m1_pre_topc @ X47 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X47)
% 1.93/2.16          | ~ (l1_pre_topc @ X48)
% 1.93/2.16          | (v2_struct_0 @ X48)
% 1.93/2.16          | (v2_struct_0 @ X49)
% 1.93/2.16          | ~ (m1_pre_topc @ X49 @ X48)
% 1.93/2.16          | ~ (v2_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49)))),
% 1.93/2.16      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.16  thf('100', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.16        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.16      inference('sup-', [status(thm)], ['98', '99'])).
% 1.93/2.16  thf('101', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('103', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('104', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.16        | (v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B))),
% 1.93/2.16      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 1.93/2.16  thf('105', plain,
% 1.93/2.16      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('simplify', [status(thm)], ['104'])).
% 1.93/2.16  thf('106', plain,
% 1.93/2.16      ((![X53 : $i]:
% 1.93/2.16          (((X53) != (sk_D)) | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B))))
% 1.93/2.16         <= ((![X53 : $i]:
% 1.93/2.16                (((X53) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.16      inference('split', [status(esa)], ['77'])).
% 1.93/2.16  thf('107', plain,
% 1.93/2.16      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))
% 1.93/2.16         <= ((![X53 : $i]:
% 1.93/2.16                (((X53) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.16      inference('simplify', [status(thm)], ['106'])).
% 1.93/2.16  thf('108', plain,
% 1.93/2.16      ((((v2_struct_0 @ sk_C)
% 1.93/2.16         | (v2_struct_0 @ sk_A)
% 1.93/2.16         | (v2_struct_0 @ sk_B)
% 1.93/2.16         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.93/2.16         <= ((![X53 : $i]:
% 1.93/2.16                (((X53) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.16      inference('sup-', [status(thm)], ['105', '107'])).
% 1.93/2.16  thf('109', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('110', plain,
% 1.93/2.16      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.93/2.16         <= ((![X53 : $i]:
% 1.93/2.16                (((X53) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.16      inference('sup-', [status(thm)], ['108', '109'])).
% 1.93/2.16  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('112', plain,
% 1.93/2.16      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.93/2.16         <= ((![X53 : $i]:
% 1.93/2.16                (((X53) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.16      inference('clc', [status(thm)], ['110', '111'])).
% 1.93/2.16  thf('113', plain, (~ (v2_struct_0 @ sk_C)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('114', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_A))
% 1.93/2.16         <= ((![X53 : $i]:
% 1.93/2.16                (((X53) != (sk_D))
% 1.93/2.16                 | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.16      inference('clc', [status(thm)], ['112', '113'])).
% 1.93/2.16  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('116', plain,
% 1.93/2.16      (~
% 1.93/2.16       (![X53 : $i]:
% 1.93/2.16          (((X53) != (sk_D)) | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B))))),
% 1.93/2.16      inference('sup-', [status(thm)], ['114', '115'])).
% 1.93/2.16  thf('117', plain,
% 1.93/2.16      ((![X54 : $i]:
% 1.93/2.16          (((X54) != (sk_D)) | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ sk_C)))) | 
% 1.93/2.16       (![X53 : $i]:
% 1.93/2.16          (((X53) != (sk_D)) | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_B))))),
% 1.93/2.16      inference('split', [status(esa)], ['77'])).
% 1.93/2.16  thf('118', plain,
% 1.93/2.16      ((![X54 : $i]:
% 1.93/2.16          (((X54) != (sk_D)) | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ sk_C))))),
% 1.93/2.16      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 1.93/2.16  thf('119', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 1.93/2.16      inference('simpl_trail', [status(thm)], ['79', '118'])).
% 1.93/2.16  thf('120', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_C)
% 1.93/2.16        | (v2_struct_0 @ sk_A)
% 1.93/2.16        | (v2_struct_0 @ sk_B)
% 1.93/2.16        | (r1_tsep_1 @ sk_B @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['76', '119'])).
% 1.93/2.16  thf('121', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('122', plain,
% 1.93/2.16      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.93/2.16      inference('sup-', [status(thm)], ['120', '121'])).
% 1.93/2.16  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('124', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.93/2.16      inference('clc', [status(thm)], ['122', '123'])).
% 1.93/2.16  thf('125', plain, (~ (v2_struct_0 @ sk_C)),
% 1.93/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.16  thf('126', plain, ((v2_struct_0 @ sk_A)),
% 1.93/2.16      inference('clc', [status(thm)], ['124', '125'])).
% 1.93/2.16  thf('127', plain, ($false), inference('demod', [status(thm)], ['0', '126'])).
% 1.93/2.16  
% 1.93/2.16  % SZS output end Refutation
% 1.93/2.16  
% 1.93/2.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

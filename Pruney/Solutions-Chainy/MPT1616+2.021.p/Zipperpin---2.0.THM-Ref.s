%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.leNyUBhzkY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 115 expanded)
%              Number of leaves         :   45 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  519 ( 854 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ~ ( v2_pre_topc @ X37 )
      | ( r2_hidden @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X40 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ ( k3_tarski @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X37: $i] :
      ( ~ ( v2_pre_topc @ X37 )
      | ( r2_hidden @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('19',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X41 ) @ X41 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X41 ) )
        = ( k3_tarski @ X41 ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X41: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X41 ) )
        = ( k3_tarski @ X41 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X41 ) @ X41 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('25',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('26',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('29',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('33',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.leNyUBhzkY
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 95 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.50  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.50  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.50  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.20/0.50  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.20/0.50  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.20/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(d1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.50         ( ( ![B:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ![C:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.50                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.50                     ( r2_hidden @
% 0.20/0.50                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.20/0.50                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.20/0.50           ( ![B:$i]:
% 0.20/0.50             ( ( m1_subset_1 @
% 0.20/0.50                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.50                 ( r2_hidden @
% 0.20/0.50                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.50                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.20/0.50           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_1, axiom,
% 0.20/0.50    (![B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.20/0.50       ( ( m1_subset_1 @
% 0.20/0.50           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.20/0.50  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.20/0.50       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.50         ( r2_hidden @
% 0.20/0.50           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_5, axiom,
% 0.20/0.50    (![B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.20/0.50       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_7, axiom,
% 0.20/0.50    (![C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.20/0.50       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.20/0.50  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_9, axiom,
% 0.20/0.50    (![C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.20/0.50       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.50         ( r2_hidden @
% 0.20/0.50           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_11, axiom,
% 0.20/0.50    (![C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.20/0.50       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.50         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_12, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.50         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.50           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.20/0.50           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X37 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ X37)
% 0.20/0.50          | (r2_hidden @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 0.20/0.50          | ~ (l1_pre_topc @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('2', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.50  thf(t56_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.50       ( r1_tarski @ C @ B ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k3_tarski @ X12) @ X13)
% 0.20/0.50          | ~ (r2_hidden @ X14 @ X12)
% 0.20/0.50          | (r1_tarski @ X14 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.50  thf(dt_u1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( u1_pre_topc @ A ) @ 
% 0.20/0.50         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X40 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_pre_topc @ X40) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.20/0.50          | ~ (l1_pre_topc @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(t95_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((r1_tarski @ (k3_tarski @ X6) @ (k3_tarski @ X7))
% 0.20/0.50          | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.20/0.50             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t99_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.50  thf('11', plain, (![X8 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X8)) = (X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X3 : $i, X5 : $i]:
% 0.20/0.50         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.50               (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X37 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ X37)
% 0.20/0.50          | (r2_hidden @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 0.20/0.50          | ~ (l1_pre_topc @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf(t14_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.50         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X41 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k3_tarski @ X41) @ X41)
% 0.20/0.50          | ((k4_yellow_0 @ (k2_yellow_1 @ X41)) = (k3_tarski @ X41))
% 0.20/0.50          | (v1_xboole_0 @ X41))),
% 0.20/0.50      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X41 : $i]:
% 0.20/0.50         (((k4_yellow_0 @ (k2_yellow_1 @ X41)) = (k3_tarski @ X41))
% 0.20/0.50          | ~ (r2_hidden @ (k3_tarski @ X41) @ X41))),
% 0.20/0.50      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.20/0.50              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.20/0.50              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.20/0.50            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.50  thf(t24_yellow_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.50         ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf(zf_stmt_13, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.50            ( u1_struct_0 @ A ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.20/0.50         != (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '29'])).
% 0.20/0.50  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('33', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.50  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

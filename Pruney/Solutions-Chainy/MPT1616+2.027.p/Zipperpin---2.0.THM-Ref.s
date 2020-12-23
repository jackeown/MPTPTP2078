%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2sI4rayII5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 122 expanded)
%              Number of leaves         :   45 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  546 ( 903 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( r1_tarski @ X11 @ X10 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ ( k3_tarski @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
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
    ! [X5: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('21',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X41: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X41 ) )
        = ( k3_tarski @ X41 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X41 ) @ X41 ) ) ),
    inference(clc,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

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

thf('29',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('30',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('33',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('37',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2sI4rayII5
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:03:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 95 iterations in 0.054s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.51  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.22/0.51  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.22/0.51  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.22/0.51  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(d1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ( v2_pre_topc @ A ) <=>
% 0.22/0.51         ( ( ![B:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ![C:$i]:
% 0.22/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.22/0.51                     ( r2_hidden @
% 0.22/0.51                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.22/0.51                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.22/0.51           ( ![B:$i]:
% 0.22/0.51             ( ( m1_subset_1 @
% 0.22/0.51                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.51               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.22/0.51                 ( r2_hidden @
% 0.22/0.51                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.51                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.22/0.51           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_1, axiom,
% 0.22/0.51    (![B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.22/0.51       ( ( m1_subset_1 @
% 0.22/0.51           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.51         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_3, axiom,
% 0.22/0.51    (![B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.22/0.51       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.22/0.51         ( r2_hidden @
% 0.22/0.51           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_5, axiom,
% 0.22/0.51    (![B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.22/0.51       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_7, axiom,
% 0.22/0.51    (![C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.22/0.51       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_9, axiom,
% 0.22/0.51    (![C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.22/0.51       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.22/0.51         ( r2_hidden @
% 0.22/0.51           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_11, axiom,
% 0.22/0.51    (![C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.22/0.51       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_12, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ( v2_pre_topc @ A ) <=>
% 0.22/0.51         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.22/0.51           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X37 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ X37)
% 0.22/0.51          | (r2_hidden @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 0.22/0.51          | ~ (l1_pre_topc @ X37))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.22/0.51  thf(d10_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.51  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.51  thf(t56_setfam_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.51       ( r1_tarski @ C @ B ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k3_tarski @ X9) @ X10)
% 0.22/0.51          | ~ (r2_hidden @ X11 @ X9)
% 0.22/0.51          | (r1_tarski @ X11 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.51  thf(dt_u1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( m1_subset_1 @
% 0.22/0.51         ( u1_pre_topc @ A ) @ 
% 0.22/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X40 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (u1_pre_topc @ X40) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.22/0.51          | ~ (l1_pre_topc @ X40))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X0)
% 0.22/0.51          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf(t95_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.51       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         ((r1_tarski @ (k3_tarski @ X3) @ (k3_tarski @ X4))
% 0.22/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X0)
% 0.22/0.51          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.22/0.51             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf(t99_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.22/0.51  thf('11', plain, (![X5 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X5)) = (X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X0)
% 0.22/0.51          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.22/0.51               (k3_tarski @ (u1_pre_topc @ X0)))
% 0.22/0.51          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.22/0.51          | ~ (l1_pre_topc @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X37 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ X37)
% 0.22/0.51          | (r2_hidden @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 0.22/0.51          | ~ (l1_pre_topc @ X37))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.51  thf(t14_yellow_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.22/0.51         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X41 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k3_tarski @ X41) @ X41)
% 0.22/0.51          | ((k4_yellow_0 @ (k2_yellow_1 @ X41)) = (k3_tarski @ X41))
% 0.22/0.51          | (v1_xboole_0 @ X41))),
% 0.22/0.51      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.22/0.51  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X6 : $i, X8 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf(t5_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X12 @ X13)
% 0.22/0.51          | ~ (v1_xboole_0 @ X14)
% 0.22/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X41 : $i]:
% 0.22/0.51         (((k4_yellow_0 @ (k2_yellow_1 @ X41)) = (k3_tarski @ X41))
% 0.22/0.51          | ~ (r2_hidden @ (k3_tarski @ X41) @ X41))),
% 0.22/0.51      inference('clc', [status(thm)], ['19', '24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.22/0.51              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '25'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.22/0.51              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.22/0.51            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.51  thf(t24_yellow_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.22/0.51         ( u1_struct_0 @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_13, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.22/0.51            ( u1_struct_0 @ A ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.22/0.51         != (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ~ (v2_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.22/0.51  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.22/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '33'])).
% 0.22/0.51  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.22/0.51  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.22/0.51  thf('37', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.51  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VbPRsSMADE

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 206 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  624 (2295 expanded)
%              Number of equality atoms :   36 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_tops_1 @ X11 @ X10 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_pre_topc @ X11 @ X10 ) @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X8 @ X9 )
      | ( ( k2_pre_topc @ X9 @ X8 )
        = X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k7_subset_1 @ X6 @ X5 @ X7 )
        = ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('24',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X12 @ ( k2_tops_1 @ X13 @ X12 ) )
      | ( v2_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_tops_1 @ X16 @ X17 )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('43',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['23','43'])).

thf('45',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['22','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_tops_1 @ X13 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tops_1 @ X14 @ X15 )
      | ~ ( v3_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('59',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['23','43','58'])).

thf('60',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['46','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VbPRsSMADE
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 42 iterations in 0.019s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(t94_tops_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.47             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( l1_pre_topc @ A ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47              ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.47                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(l78_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.47             ( k7_subset_1 @
% 0.19/0.47               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.19/0.47               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.47          | ((k2_tops_1 @ X11 @ X10)
% 0.19/0.47              = (k7_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.19/0.47                 (k2_pre_topc @ X11 @ X10) @ (k1_tops_1 @ X11 @ X10)))
% 0.19/0.47          | ~ (l1_pre_topc @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.47            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.47               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t52_pre_topc, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.19/0.47             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.19/0.47               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.47          | ~ (v4_pre_topc @ X8 @ X9)
% 0.19/0.47          | ((k2_pre_topc @ X9 @ X8) = (X8))
% 0.19/0.47          | ~ (l1_pre_topc @ X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.19/0.47        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.47         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.47            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('demod', [status(thm)], ['2', '3', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.47          | ((k7_subset_1 @ X6 @ X5 @ X7) = (k4_xboole_0 @ X5 @ X7)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.47           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.47         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '13'])).
% 0.19/0.47  thf(t36_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.19/0.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.47  thf(d10_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X2 : $i]:
% 0.19/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.47          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.47        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.47         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '13'])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.47        | ((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.47         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.47         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('split', [status(esa)], ['24'])).
% 0.19/0.47  thf('26', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t88_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( v2_tops_1 @ B @ A ) <=>
% 0.19/0.47             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.47          | ~ (r1_tarski @ X12 @ (k2_tops_1 @ X13 @ X12))
% 0.19/0.47          | (v2_tops_1 @ X12 @ X13)
% 0.19/0.47          | ~ (l1_pre_topc @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | (v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.47        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.47  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (((v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.47        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.19/0.47         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['25', '30'])).
% 0.19/0.47  thf('32', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.47  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('demod', [status(thm)], ['31', '33'])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t93_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.19/0.47             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('36', plain,
% 0.19/0.47      (![X16 : $i, X17 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.47          | (v3_tops_1 @ X16 @ X17)
% 0.19/0.47          | ~ (v4_pre_topc @ X16 @ X17)
% 0.19/0.47          | ~ (v2_tops_1 @ X16 @ X17)
% 0.19/0.47          | ~ (l1_pre_topc @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [t93_tops_1])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.47        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.19/0.47        | (v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.47  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('39', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('40', plain, ((~ (v2_tops_1 @ sk_B @ sk_A) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['34', '40'])).
% 0.19/0.47  thf('42', plain,
% 0.19/0.47      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('43', plain,
% 0.19/0.47      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.47  thf('44', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['23', '43'])).
% 0.19/0.47  thf('45', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['22', '44'])).
% 0.19/0.47  thf('46', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['20', '45'])).
% 0.19/0.47  thf('47', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('48', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.47          | ~ (v2_tops_1 @ X12 @ X13)
% 0.19/0.47          | (r1_tarski @ X12 @ (k2_tops_1 @ X13 @ X12))
% 0.19/0.47          | ~ (l1_pre_topc @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.19/0.47  thf('49', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.47        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.47  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('51', plain,
% 0.19/0.47      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['24'])).
% 0.19/0.47  thf('52', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t92_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('53', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.47          | (v2_tops_1 @ X14 @ X15)
% 0.19/0.47          | ~ (v3_tops_1 @ X14 @ X15)
% 0.19/0.47          | ~ (l1_pre_topc @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.19/0.47  thf('54', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.19/0.47        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.47  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('56', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.47  thf('57', plain,
% 0.19/0.47      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['51', '56'])).
% 0.19/0.47  thf('58', plain,
% 0.19/0.47      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('split', [status(esa)], ['24'])).
% 0.19/0.47  thf('59', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['23', '43', '58'])).
% 0.19/0.47  thf('60', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.19/0.47  thf('61', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['49', '50', '60'])).
% 0.19/0.47  thf('62', plain, ($false), inference('demod', [status(thm)], ['46', '61'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

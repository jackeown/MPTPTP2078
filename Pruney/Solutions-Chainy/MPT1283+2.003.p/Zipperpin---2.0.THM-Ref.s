%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqTxYZNzFW

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 144 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  563 (1633 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t105_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( ( v5_tops_1 @ B @ A )
            <=> ( v6_tops_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v4_pre_topc @ B @ A ) )
             => ( ( v5_tops_1 @ B @ A )
              <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t105_tops_1])).

thf('0',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
   <= ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v6_tops_1 @ X7 @ X8 )
      | ( X7
        = ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v4_pre_topc @ X3 @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
        = X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','14'])).

thf('16',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X5
       != ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ( v5_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( sk_B
       != ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v5_tops_1 @ sk_B @ sk_A ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('24',plain,
    ( ( ( sk_B != sk_B )
      | ( v5_tops_1 @ sk_B @ sk_A ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( v5_tops_1 @ sk_B @ sk_A )
   <= ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7
       != ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ( v6_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('35',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ X11 @ ( k1_tops_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','52'])).

thf('54',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['35','54'])).

thf('56',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['29','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqTxYZNzFW
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 41 iterations in 0.022s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(t105_tops_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.47             ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( l1_pre_topc @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.47                ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t105_tops_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((~ (v6_tops_1 @ sk_B @ sk_A) | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((~ (v6_tops_1 @ sk_B @ sk_A)) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (~ ((v6_tops_1 @ sk_B @ sk_A)) | ~ ((v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain, (((v6_tops_1 @ sk_B @ sk_A) | (v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((v6_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d8_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v6_tops_1 @ B @ A ) <=>
% 0.20/0.48             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.48          | ~ (v6_tops_1 @ X7 @ X8)
% 0.20/0.48          | ((X7) = (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.20/0.48          | ~ (l1_pre_topc @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.48        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t52_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (v4_pre_topc @ X3 @ X4)
% 0.20/0.48          | ((k2_pre_topc @ X4 @ X3) = (X3))
% 0.20/0.48          | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)) | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B))) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d7_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v5_tops_1 @ B @ A ) <=>
% 0.20/0.48             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.48          | ((X5) != (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.20/0.48          | (v5_tops_1 @ X5 @ X6)
% 0.20/0.48          | ~ (l1_pre_topc @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v5_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((((sk_B) != (k2_pre_topc @ sk_A @ sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.48  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((((sk_B) != (sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((~ (v5_tops_1 @ sk_B @ sk_A)) <= (~ ((v5_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)) | ~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, (~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 0.20/0.48  thf('29', plain, (~ (v6_tops_1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.48          | ((X7) != (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.20/0.48          | (v6_tops_1 @ X7 @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v6_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_B) != (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t44_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.48          | (r1_tarski @ (k1_tops_1 @ X10 @ X9) @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i]:
% 0.20/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.48        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t56_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.48                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (v3_pre_topc @ X11 @ X12)
% 0.20/0.48          | ~ (r1_tarski @ X11 @ X13)
% 0.20/0.48          | (r1_tarski @ X11 @ (k1_tops_1 @ X12 @ X13))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (l1_pre_topc @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.48          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.48          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.48          | ~ (r1_tarski @ sk_B @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.48        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.48      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.48  thf('53', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['50', '52'])).
% 0.20/0.48  thf('54', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '53'])).
% 0.20/0.48  thf('55', plain, (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['35', '54'])).
% 0.20/0.48  thf('56', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.48  thf('57', plain, ($false), inference('demod', [status(thm)], ['29', '56'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

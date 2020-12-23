%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dYDFW6BCdE

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 113 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  438 ( 867 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( ( k1_tops_1 @ X15 @ ( k2_struct_0 @ X15 ) )
        = ( k2_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('40',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('46',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dYDFW6BCdE
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 124 iterations in 0.055s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.53  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(t35_connsp_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d3_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d2_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X5 @ X6)
% 0.21/0.53          | (r2_hidden @ X5 @ X6)
% 0.21/0.53          | (v1_xboole_0 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(d1_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X3 @ X2)
% 0.21/0.53          | (r1_tarski @ X3 @ X1)
% 0.21/0.53          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.53  thf(dt_k2_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.53  thf('10', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('11', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '14'])).
% 0.21/0.53  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.53  thf(t43_tops_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X15 : $i]:
% 0.21/0.53         (((k1_tops_1 @ X15 @ (k2_struct_0 @ X15)) = (k2_struct_0 @ X15))
% 0.21/0.53          | ~ (l1_pre_topc @ X15)
% 0.21/0.53          | ~ (v2_pre_topc @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('22', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d2_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.53          | ~ (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.21/0.53          | (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.21/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.53          | ~ (l1_pre_topc @ X17)
% 0.21/0.53          | ~ (v2_pre_topc @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.53        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '29'])).
% 0.21/0.53  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.21/0.53        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '32'])).
% 0.21/0.53  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.53        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '37'])).
% 0.21/0.53  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X14 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.21/0.53          | ~ (l1_struct_0 @ X14)
% 0.21/0.53          | (v2_struct_0 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('44', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('46', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

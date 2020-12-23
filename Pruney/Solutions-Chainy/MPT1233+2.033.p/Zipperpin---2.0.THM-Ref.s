%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXuPgqLurk

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 141 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  512 ( 852 expanded)
%              Number of equality atoms :   45 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_struct_0 @ X15 ) ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('12',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','51'])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('55',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXuPgqLurk
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:36:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 267 iterations in 0.116s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.57  thf(fc3_struct_0, axiom,
% 0.38/0.57    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ (k1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.38/0.57  thf(l13_xboole_0, axiom,
% 0.38/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_struct_0 @ X0) | ((k1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf(t27_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_struct_0 @ A ) =>
% 0.38/0.57       ( ( k2_struct_0 @ A ) =
% 0.38/0.57         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X15 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X15)
% 0.38/0.57            = (k3_subset_1 @ (u1_struct_0 @ X15) @ (k1_struct_0 @ X15)))
% 0.38/0.57          | ~ (l1_struct_0 @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X0)
% 0.38/0.57            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('5', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.38/0.57  thf(t22_subset_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.38/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.57  thf('7', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.38/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['5', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['4', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.57  thf(t43_tops_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.57  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf(t4_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf(cc2_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.57          | (v4_pre_topc @ X11 @ X12)
% 0.38/0.57          | ~ (v1_xboole_0 @ X11)
% 0.38/0.57          | ~ (l1_pre_topc @ X12)
% 0.38/0.57          | ~ (v2_pre_topc @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_pre_topc @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.57          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.57  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_pre_topc @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X0)
% 0.38/0.57          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((v4_pre_topc @ X0 @ X1)
% 0.38/0.57          | ~ (v1_xboole_0 @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X1)
% 0.38/0.57          | ~ (v2_pre_topc @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['15', '20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_pre_topc @ sk_A)
% 0.38/0.57          | ~ (v1_xboole_0 @ X0)
% 0.38/0.57          | (v4_pre_topc @ X0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '21'])).
% 0.38/0.57  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf(t52_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.57             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.57               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.57          | ~ (v4_pre_topc @ X16 @ X17)
% 0.38/0.57          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.38/0.57          | ~ (l1_pre_topc @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X0)
% 0.38/0.57          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.57          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.57        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '27'])).
% 0.38/0.57  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.57  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.41/0.57  thf(dt_k2_subset_1, axiom,
% 0.41/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.57  thf('32', plain,
% 0.41/0.57      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.57  thf('33', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.41/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.57  thf('34', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.41/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.57  thf(d1_tops_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_pre_topc @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57           ( ( k1_tops_1 @ A @ B ) =
% 0.41/0.57             ( k3_subset_1 @
% 0.41/0.57               ( u1_struct_0 @ A ) @ 
% 0.41/0.57               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.41/0.57  thf('35', plain,
% 0.41/0.57      (![X18 : $i, X19 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.57          | ((k1_tops_1 @ X19 @ X18)
% 0.41/0.57              = (k3_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.41/0.57                 (k2_pre_topc @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18))))
% 0.41/0.57          | ~ (l1_pre_topc @ X19))),
% 0.41/0.57      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.41/0.57  thf('36', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (~ (l1_pre_topc @ X0)
% 0.41/0.57          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.41/0.57              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.57                 (k2_pre_topc @ X0 @ 
% 0.41/0.57                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.57  thf('37', plain,
% 0.41/0.57      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.41/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.41/0.57  thf('38', plain,
% 0.41/0.57      (![X4 : $i, X5 : $i]:
% 0.41/0.57         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.41/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.41/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.41/0.57  thf('39', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.57  thf('40', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['5', '8'])).
% 0.41/0.57  thf('41', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.57  thf('42', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (~ (l1_pre_topc @ X0)
% 0.41/0.57          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.41/0.57              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.57                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.41/0.57      inference('demod', [status(thm)], ['36', '41'])).
% 0.41/0.57  thf('43', plain,
% 0.41/0.57      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.41/0.57          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.41/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.57      inference('sup+', [status(thm)], ['31', '42'])).
% 0.41/0.57  thf('44', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['5', '8'])).
% 0.41/0.57  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('46', plain,
% 0.41/0.57      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.41/0.57  thf('47', plain,
% 0.41/0.57      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.41/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.57      inference('sup+', [status(thm)], ['13', '46'])).
% 0.41/0.57  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(dt_l1_pre_topc, axiom,
% 0.41/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.57  thf('49', plain,
% 0.41/0.57      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.57  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.57  thf('51', plain,
% 0.41/0.57      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['47', '50'])).
% 0.41/0.57  thf('52', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['12', '51'])).
% 0.41/0.57  thf('53', plain,
% 0.41/0.57      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.57      inference('sup-', [status(thm)], ['11', '52'])).
% 0.41/0.57  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.57  thf('55', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.41/0.57  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.41/0.57  
% 0.41/0.57  % SZS output end Refutation
% 0.41/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

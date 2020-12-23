%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bL4fAodlJk

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 196 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  491 (1199 expanded)
%              Number of equality atoms :   44 ( 126 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

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

thf('1',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( ( k1_struct_0 @ X12 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('5',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('7',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ sk_A )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('13',plain,(
    ! [X5: $i] :
      ( X5
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('17',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X4 @ ( k3_subset_1 @ X4 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,(
    ! [X5: $i] :
      ( X5
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('30',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

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

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v4_pre_topc @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','47','48','49'])).

thf('51',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bL4fAodlJk
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 216 iterations in 0.058s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('0', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.52  thf(t43_tops_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.21/0.52  thf('1', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('2', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf(d2_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (((k1_struct_0 @ X12) = (k1_xboole_0)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.21/0.52  thf('5', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(t27_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) =>
% 0.21/0.52       ( ( k2_struct_0 @ A ) =
% 0.21/0.52         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X14 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X14)
% 0.21/0.52            = (k3_subset_1 @ (u1_struct_0 @ X14) @ (k1_struct_0 @ X14)))
% 0.21/0.52          | ~ (l1_struct_0 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((((k2_struct_0 @ sk_A)
% 0.21/0.52          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (((k2_struct_0 @ sk_A)
% 0.21/0.52         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k2_struct_0 @ sk_A)
% 0.21/0.52           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_subset_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['0', '9'])).
% 0.21/0.52  thf(t22_subset_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X5 : $i]:
% 0.21/0.52         ((k2_subset_1 @ X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.52  thf('12', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X5 : $i]: ((X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.52  thf(dt_k2_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.52  thf('16', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('17', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf(d1_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.52             ( k3_subset_1 @
% 0.21/0.52               ( u1_struct_0 @ A ) @ 
% 0.21/0.52               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.52          | ((k1_tops_1 @ X18 @ X17)
% 0.21/0.52              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.21/0.52                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 0.21/0.52          | ~ (l1_pre_topc @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.21/0.52              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.52                 (k2_pre_topc @ X0 @ 
% 0.21/0.52                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf(t4_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (((k3_subset_1 @ X4 @ (k3_subset_1 @ X4 @ X3)) = (X3))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X5 : $i]: ((X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('25', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['22', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.21/0.52              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.52                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['19', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.21/0.52          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ k1_xboole_0)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '27'])).
% 0.21/0.52  thf('29', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf('31', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.52  thf(t52_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (v4_pre_topc @ X15 @ X16)
% 0.21/0.52          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.21/0.52          | ~ (l1_pre_topc @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.21/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.21/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((~ (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 0.21/0.52        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf('38', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.52  thf(cc2_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | (v4_pre_topc @ X10 @ X11)
% 0.21/0.52          | ~ (v1_xboole_0 @ X10)
% 0.21/0.52          | ~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((v4_pre_topc @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '43'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('46', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '46'])).
% 0.21/0.52  thf('48', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '47', '48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

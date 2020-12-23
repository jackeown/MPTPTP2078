%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F9oIdpc6Zv

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  396 ( 438 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ X15 @ ( k2_pre_topc @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( ( k7_subset_1 @ X4 @ X3 @ X5 )
        = ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t23_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B
                 != ( k2_struct_0 @ A ) )
                & ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B )
                  = k1_xboole_0 ) )
            & ~ ( ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B )
                 != k1_xboole_0 )
                & ( B
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_struct_0 @ X14 ) @ X13 )
       != k1_xboole_0 )
      | ( X13
        = ( k2_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t27_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tops_1])).

thf('23',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F9oIdpc6Zv
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 35 iterations in 0.024s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(dt_k2_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( m1_subset_1 @
% 0.22/0.49         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X9 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.49          | ~ (l1_struct_0 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.22/0.49  thf(t48_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.49          | (r1_tarski @ X15 @ (k2_pre_topc @ X16 @ X15))
% 0.22/0.49          | ~ (l1_pre_topc @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | (r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.22/0.49             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(dt_l1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.49  thf('3', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.22/0.49           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(l32_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ((k4_xboole_0 @ (k2_struct_0 @ X0) @ 
% 0.22/0.49              (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X9 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.49          | ~ (l1_struct_0 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.22/0.49  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.49          | ((k7_subset_1 @ X4 @ X3 @ X5) = (k4_xboole_0 @ X3 @ X5)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X0)
% 0.22/0.49          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.22/0.49              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X9 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.49          | ~ (l1_struct_0 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.22/0.49  thf(dt_k2_pre_topc, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( m1_subset_1 @
% 0.22/0.49         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X7)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.49          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X0)
% 0.22/0.49          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.49      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf(t23_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( ~( ( ( B ) != ( k2_struct_0 @ A ) ) & 
% 0.22/0.49                  ( ( k7_subset_1 @
% 0.22/0.49                      ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) =
% 0.22/0.49                    ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.49             ( ~( ( ( k7_subset_1 @
% 0.22/0.49                      ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) !=
% 0.22/0.49                    ( k1_xboole_0 ) ) & 
% 0.22/0.49                  ( ( B ) = ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.49          | ((k7_subset_1 @ (u1_struct_0 @ X14) @ (k2_struct_0 @ X14) @ X13)
% 0.22/0.49              != (k1_xboole_0))
% 0.22/0.49          | ((X13) = (k2_struct_0 @ X14))
% 0.22/0.49          | ~ (l1_struct_0 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t23_pre_topc])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.22/0.49          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 0.22/0.49              (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))) != (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ (k2_struct_0 @ X0) @ 
% 0.22/0.49            (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))) != (k1_xboole_0))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ((k4_xboole_0 @ (k2_struct_0 @ X0) @ 
% 0.22/0.49              (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))) != (k1_xboole_0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.22/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf(t27_tops_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_pre_topc @ A ) =>
% 0.22/0.49          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('26', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

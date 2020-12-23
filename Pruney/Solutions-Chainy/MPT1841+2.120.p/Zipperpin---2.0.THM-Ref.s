%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cVbChrNpnH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  338 ( 554 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ A )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( A != k1_xboole_0 )
                   => ( m1_subset_1 @ ( k2_enumset1 @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( m1_subset_1 @ ( k2_enumset1 @ X10 @ X7 @ X11 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t58_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_enumset1 @ X0 @ sk_B @ X1 @ X2 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k2_enumset1 @ sk_B @ sk_B @ X1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k1_enumset1 @ sk_B @ X1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_enumset1 @ sk_B @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_enumset1 @ sk_B @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_zfmisc_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('21',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['27','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cVbChrNpnH
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:51:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 22 iterations in 0.015s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(t6_tex_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.51           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.51                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.51              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.51                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t58_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.51           ( ![D:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.51               ( ![E:$i]:
% 0.22/0.51                 ( ( m1_subset_1 @ E @ A ) =>
% 0.22/0.51                   ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.51                     ( m1_subset_1 @
% 0.22/0.51                       ( k2_enumset1 @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X7 @ X8)
% 0.22/0.51          | ~ (m1_subset_1 @ X9 @ X8)
% 0.22/0.51          | (m1_subset_1 @ (k2_enumset1 @ X10 @ X7 @ X11 @ X9) @ 
% 0.22/0.51             (k1_zfmisc_1 @ X8))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ X8)
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t58_subset_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.22/0.51          | ((sk_A) = (k1_xboole_0))
% 0.22/0.51          | (m1_subset_1 @ (k2_enumset1 @ X0 @ sk_B @ X1 @ X2) @ 
% 0.22/0.51             (k1_zfmisc_1 @ sk_A))
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.51          | (m1_subset_1 @ (k2_enumset1 @ sk_B @ sk_B @ X1 @ X0) @ 
% 0.22/0.51             (k1_zfmisc_1 @ sk_A))
% 0.22/0.51          | ((sk_A) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.51  thf(t71_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.51          | (m1_subset_1 @ (k1_enumset1 @ sk_B @ X1 @ X0) @ 
% 0.22/0.51             (k1_zfmisc_1 @ sk_A))
% 0.22/0.51          | ((sk_A) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.51          | ((sk_A) = (k1_xboole_0))
% 0.22/0.51          | (m1_subset_1 @ (k1_enumset1 @ sk_B @ X0 @ sk_B) @ 
% 0.22/0.51             (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (((m1_subset_1 @ (k1_enumset1 @ sk_B @ sk_B @ sk_B) @ 
% 0.22/0.51         (k1_zfmisc_1 @ sk_A))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '10'])).
% 0.22/0.51  thf(t70_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i]:
% 0.22/0.51         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('13', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.51  thf(cc2_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.22/0.51          | ~ (v1_subset_1 @ X16 @ X17)
% 0.22/0.51          | (v1_xboole_0 @ X16)
% 0.22/0.51          | ~ (v1_zfmisc_1 @ X17)
% 0.22/0.51          | (v1_xboole_0 @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((((sk_A) = (k1_xboole_0))
% 0.22/0.51        | (v1_xboole_0 @ sk_A)
% 0.22/0.51        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.22/0.51        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X14)
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ X14)
% 0.22/0.51          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.51        | (v1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('23', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.51      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((((sk_A) = (k1_xboole_0))
% 0.22/0.51        | (v1_xboole_0 @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17', '24'])).
% 0.22/0.51  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((v1_xboole_0 @ (k1_tarski @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.51  thf('28', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.51  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.51  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.51  thf('31', plain, ($false),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '29', '30'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

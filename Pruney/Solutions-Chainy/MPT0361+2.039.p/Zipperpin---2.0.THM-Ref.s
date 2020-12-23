%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GsEvqrAyB4

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:55 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  342 ( 682 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X15 @ X14 ) @ X16 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X15 @ X16 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['6','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GsEvqrAyB4
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 316 iterations in 0.256s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.50/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(t41_subset_1, conjecture,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72           ( r1_tarski @
% 0.50/0.72             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.50/0.72             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i]:
% 0.50/0.72        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72          ( ![C:$i]:
% 0.50/0.72            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72              ( r1_tarski @
% 0.50/0.72                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.50/0.72                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.50/0.72  thf('0', plain,
% 0.50/0.72      (~ (r1_tarski @ 
% 0.50/0.72          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.50/0.72          (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(redefinition_k4_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.50/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.50/0.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.50/0.72          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.50/0.72  thf('4', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.50/0.72      inference('sup-', [status(thm)], ['1', '4'])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.50/0.72          (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.72      inference('demod', [status(thm)], ['0', '5'])).
% 0.50/0.72  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(involutiveness_k3_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]:
% 0.50/0.72         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 0.50/0.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.50/0.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.50/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('10', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(dt_k4_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.50/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.50/0.72          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.50/0.72          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.50/0.72           (k1_zfmisc_1 @ sk_A))
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['10', '13'])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.50/0.72      inference('sup-', [status(thm)], ['1', '4'])).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('demod', [status(thm)], ['14', '15'])).
% 0.50/0.72  thf(t36_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.50/0.72             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.50/0.72          | (r1_tarski @ (k3_subset_1 @ X15 @ X14) @ X16)
% 0.50/0.72          | ~ (r1_tarski @ (k3_subset_1 @ X15 @ X16) @ X14)
% 0.50/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.50/0.72  thf('18', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.72          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.50/0.72               (k2_xboole_0 @ sk_B @ sk_C))
% 0.50/0.72          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.50/0.72             X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.50/0.72        | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.50/0.72           (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.72        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['9', '18'])).
% 0.50/0.72  thf(t7_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.72  thf('20', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.72  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(dt_k3_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (![X4 : $i, X5 : $i]:
% 0.50/0.72         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.50/0.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.50/0.72        (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.72      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.50/0.72  thf('25', plain, ($false), inference('demod', [status(thm)], ['6', '24'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.60/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

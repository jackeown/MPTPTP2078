%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a9qIAFohML

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:59 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 108 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  468 (1128 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t42_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('21',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ X16 @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','36'])).

thf('38',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['14','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a9qIAFohML
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 215 iterations in 0.106s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(t42_subset_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60           ( r1_tarski @
% 0.41/0.60             ( k3_subset_1 @ A @ B ) @ 
% 0.41/0.60             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i]:
% 0.41/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60          ( ![C:$i]:
% 0.41/0.60            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60              ( r1_tarski @
% 0.41/0.60                ( k3_subset_1 @ A @ B ) @ 
% 0.41/0.60                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.41/0.60          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d5_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.41/0.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k9_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 0.41/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (m1_subset_1 @ (k9_subset_1 @ sk_A @ X0 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.41/0.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ X0 @ sk_C))
% 0.41/0.60           = (k4_xboole_0 @ sk_A @ (k9_subset_1 @ sk_A @ X0 @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60          (k4_xboole_0 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['4', '9'])).
% 0.41/0.60  thf('11', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k9_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.60         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.41/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k9_subset_1 @ sk_A @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60          (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['10', '13'])).
% 0.41/0.60  thf(t17_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.41/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (m1_subset_1 @ (k9_subset_1 @ sk_A @ X0 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k9_subset_1 @ sk_A @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k3_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.41/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf(t35_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.41/0.60             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.41/0.60          | (r1_tarski @ X16 @ (k3_subset_1 @ X17 @ X18))
% 0.41/0.60          | ~ (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.41/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.60          | ~ (r1_tarski @ X0 @ 
% 0.41/0.60               (k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.60          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60             (k3_subset_1 @ sk_A @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(involutiveness_k3_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.41/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.41/0.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.60          | ~ (r1_tarski @ X0 @ sk_B)
% 0.41/0.60          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60             (k3_subset_1 @ sk_A @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['25', '30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60           (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))
% 0.41/0.60          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ X0 @ sk_C))
% 0.41/0.60           = (k4_xboole_0 @ sk_A @ (k9_subset_1 @ sk_A @ X0 @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k9_subset_1 @ sk_A @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k9_subset_1 @ sk_A @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))
% 0.41/0.60           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60           (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))
% 0.41/0.60          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['32', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.60        (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '37'])).
% 0.41/0.60  thf('39', plain, ($false), inference('demod', [status(thm)], ['14', '38'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sGuU57SfMu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   49 (  84 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  360 ( 843 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X4 @ X3 ) @ ( k4_xboole_0 @ X4 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['8','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sGuU57SfMu
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 251 iterations in 0.174s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.60  thf(t41_subset_1, conjecture,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.60       ( ![C:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.60           ( r1_tarski @
% 0.38/0.60             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.38/0.60             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i]:
% 0.38/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.60          ( ![C:$i]:
% 0.38/0.60            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.60              ( r1_tarski @
% 0.38/0.60                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.38/0.60                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (~ (r1_tarski @ 
% 0.38/0.60          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.38/0.60          (k3_subset_1 @ sk_A @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.60       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.38/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.38/0.60          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.38/0.60          (k3_subset_1 @ sk_A @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '7'])).
% 0.38/0.60  thf('9', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_k4_subset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.38/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.38/0.60          | (m1_subset_1 @ (k4_subset_1 @ X13 @ X12 @ X14) @ 
% 0.38/0.60             (k1_zfmisc_1 @ X13)))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.38/0.60           (k1_zfmisc_1 @ sk_A))
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '12'])).
% 0.38/0.60  thf(d5_subset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i]:
% 0.38/0.60         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.38/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (((k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C))
% 0.38/0.60         = (k4_xboole_0 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 0.38/0.60         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.38/0.60  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i]:
% 0.38/0.60         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.38/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.60  thf(t36_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.38/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.60  thf(t44_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.38/0.60       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.60         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.38/0.60          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf(t34_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.60       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X2 @ X3)
% 0.38/0.60          | (r1_tarski @ (k4_xboole_0 @ X4 @ X3) @ (k4_xboole_0 @ X4 @ X2)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.38/0.60          (k4_xboole_0 @ X2 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 0.38/0.60          (k3_subset_1 @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['21', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.38/0.60        (k3_subset_1 @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['18', '27'])).
% 0.38/0.60  thf('29', plain, ($false), inference('demod', [status(thm)], ['8', '28'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

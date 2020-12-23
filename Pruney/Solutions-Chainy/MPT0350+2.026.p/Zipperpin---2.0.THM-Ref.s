%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u6kio2EKcH

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 116 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  498 ( 926 expanded)
%              Number of equality atoms :   51 (  90 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','15','20','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('36',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('44',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u6kio2EKcH
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:00:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 81 iterations in 0.036s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(t25_subset_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.48         ( k2_subset_1 @ A ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.48            ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.19/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_k3_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k3_subset_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.19/0.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf(d5_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.19/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.48         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X23 : $i, X24 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.19/0.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.19/0.48  thf(t39_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.19/0.48           = (k2_xboole_0 @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.19/0.48         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf(commutativity_k2_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.48  thf(l51_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i]:
% 0.19/0.48         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i]:
% 0.19/0.48         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.19/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.19/0.48           = (k2_xboole_0 @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.48         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.19/0.48         = (k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['10', '15', '20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf(t41_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.48       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.19/0.48           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.19/0.48           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf(t46_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['25', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.19/0.48           = (k2_xboole_0 @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.19/0.48         = (k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf(t1_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (((sk_A) = (k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['22', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.48         != (k2_subset_1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.48  thf('36', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.48       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.19/0.48          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.19/0.48          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.48         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.48         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.48         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.48  thf('45', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['37', '44'])).
% 0.19/0.48  thf('46', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '45'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

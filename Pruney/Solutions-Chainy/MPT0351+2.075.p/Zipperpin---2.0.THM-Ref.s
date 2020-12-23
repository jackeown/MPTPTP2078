%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u8YiTE8520

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  395 ( 662 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('0',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('5',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k3_tarski @ ( k2_tarski @ X39 @ X41 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['3','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('22',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k4_subset_1 @ X42 @ X43 @ ( k3_subset_1 @ X42 @ X43 ) )
        = ( k2_subset_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k4_subset_1 @ X42 @ X43 @ ( k3_subset_1 @ X42 @ X43 ) )
        = X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('34',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['13','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u8YiTE8520
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:50:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 69 iterations in 0.057s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(t28_subset_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.22/0.54         != (k2_subset_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.54  thf('1', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('2', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('3', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.22/0.54  thf(dt_k2_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X36 : $i]: (m1_subset_1 @ (k2_subset_1 @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.54  thf('5', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('6', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.22/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 0.22/0.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 0.22/0.54          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.54  thf(l51_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X31 : $i, X32 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 0.22/0.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 0.22/0.54          | ((k4_subset_1 @ X40 @ X39 @ X41)
% 0.22/0.54              = (k3_tarski @ (k2_tarski @ X39 @ X41))))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.22/0.54            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (((k4_subset_1 @ sk_A @ sk_B @ sk_A)
% 0.22/0.54         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '11'])).
% 0.22/0.54  thf('13', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) != (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '12'])).
% 0.22/0.54  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_k3_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X37 : $i, X38 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.22/0.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d5_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X34 : $i, X35 : $i]:
% 0.22/0.54         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.22/0.54          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['16', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.22/0.54            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.54         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf(t39_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X2 : $i, X3 : $i]:
% 0.22/0.54         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.22/0.54           = (k2_xboole_0 @ X2 @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X31 : $i, X32 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X31 : $i, X32 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X2 : $i, X3 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X2 @ (k4_xboole_0 @ X3 @ X2)))
% 0.22/0.54           = (k3_tarski @ (k2_tarski @ X2 @ X3)))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.54         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['22', '26'])).
% 0.22/0.54  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t25_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.22/0.54         ( k2_subset_1 @ A ) ) ))).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         (((k4_subset_1 @ X42 @ X43 @ (k3_subset_1 @ X42 @ X43))
% 0.22/0.54            = (k2_subset_1 @ X42))
% 0.22/0.54          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.22/0.54  thf('30', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         (((k4_subset_1 @ X42 @ X43 @ (k3_subset_1 @ X42 @ X43)) = (X42))
% 0.22/0.54          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.22/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) = (sk_A))),
% 0.22/0.54      inference('sup+', [status(thm)], ['27', '34'])).
% 0.22/0.54  thf('36', plain, (((sk_A) != (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '35'])).
% 0.22/0.54  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

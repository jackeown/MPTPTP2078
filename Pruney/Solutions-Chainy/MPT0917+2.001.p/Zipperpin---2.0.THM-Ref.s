%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wumwmm2Q33

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:08 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 485 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t77_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_tarski @ E @ F ) )
     => ( r1_tarski @ ( k3_zfmisc_1 @ A @ C @ E ) @ ( k3_zfmisc_1 @ B @ D @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D )
          & ( r1_tarski @ E @ F ) )
       => ( r1_tarski @ ( k3_zfmisc_1 @ A @ C @ E ) @ ( k3_zfmisc_1 @ B @ D @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_mcart_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X3 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_E ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X3 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ X0 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ X0 ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_B @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wumwmm2Q33
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 100 iterations in 0.075s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(t77_mcart_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & ( r1_tarski @ E @ F ) ) =>
% 0.36/0.56       ( r1_tarski @ ( k3_zfmisc_1 @ A @ C @ E ) @ ( k3_zfmisc_1 @ B @ D @ F ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.56        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.36/0.56            ( r1_tarski @ E @ F ) ) =>
% 0.36/0.56          ( r1_tarski @
% 0.36/0.56            ( k3_zfmisc_1 @ A @ C @ E ) @ ( k3_zfmisc_1 @ B @ D @ F ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t77_mcart_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (~ (r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.36/0.56          (k3_zfmisc_1 @ sk_B @ sk_D @ sk_F))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(d3_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.56       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.36/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.56  thf('2', plain, ((r1_tarski @ sk_E @ sk_F)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t118_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.56       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.36/0.56         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | (r1_tarski @ (k2_zfmisc_1 @ X5 @ X3) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_E) @ (k2_zfmisc_1 @ X0 @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ sk_E) @ 
% 0.36/0.56          (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ sk_F))),
% 0.36/0.56      inference('sup+', [status(thm)], ['1', '4'])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.36/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ sk_E) @ 
% 0.36/0.56          (k3_zfmisc_1 @ X1 @ X0 @ sk_F))),
% 0.36/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf('8', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | (r1_tarski @ (k2_zfmisc_1 @ X5 @ X3) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_B @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf(t1_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.56       ( r1_tarski @ A @ C ) ))).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.36/0.56          | (r1_tarski @ X0 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ X1)
% 0.36/0.56          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ X0) @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['10', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r1_tarski @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ X0) @ 
% 0.36/0.56          (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D) @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.36/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.36/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ X0) @ 
% 0.36/0.56          (k3_zfmisc_1 @ sk_B @ sk_D @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.36/0.56          | (r1_tarski @ X0 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.36/0.56          | ~ (r1_tarski @ (k3_zfmisc_1 @ sk_B @ sk_D @ X0) @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      ((r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.36/0.56        (k3_zfmisc_1 @ sk_B @ sk_D @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '23'])).
% 0.36/0.56  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jIKhvTeZGg

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 154 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 (1150 expanded)
%              Number of equality atoms :   15 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_C
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X47 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jIKhvTeZGg
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 61 iterations in 0.026s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(t47_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.48       ( r2_hidden @ A @ C ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.48          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.21/0.48  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X4 : $i, X6 : $i]:
% 0.21/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.48        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf(t38_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.48         ((r2_hidden @ X47 @ X46)
% 0.21/0.48          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 0.21/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.48         ((r2_hidden @ X45 @ X46)
% 0.21/0.48          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 0.21/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.21/0.48         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 0.21/0.48          | ~ (r2_hidden @ X47 @ X48)
% 0.21/0.48          | ~ (r2_hidden @ X45 @ X48))),
% 0.21/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.48          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X4 : $i, X6 : $i]:
% 0.21/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.21/0.48          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf(l51_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X43 : $i, X44 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X43 : $i, X44 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf(t7_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '21', '22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.48      inference('sup+', [status(thm)], ['24', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.48         ((r2_hidden @ X45 @ X46)
% 0.21/0.48          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 0.21/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.48  thf('30', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wZHufkC4l6

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  77 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  304 ( 777 expanded)
%              Number of equality atoms :   28 (  70 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t16_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('5',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ ( k2_zfmisc_1 @ X3 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_mcart_1 @ X11 )
        = X10 )
      | ( ( k1_mcart_1 @ X11 )
        = X12 )
      | ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ ( k2_tarski @ X12 @ X10 ) @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C )
    | ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['15','21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('24',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['19','24'])).

thf('26',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['23','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','22','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wZHufkC4l6
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 30 iterations in 0.014s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(t16_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.46         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.46          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.46            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t16_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t10_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.46         ((r2_hidden @ (k2_mcart_1 @ X7) @ X9)
% 0.20/0.46          | ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.46         ((r2_hidden @ (k1_mcart_1 @ X7) @ X8)
% 0.20/0.46          | ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.46  thf('5', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf(l54_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.46       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.46         ((r2_hidden @ (k4_tarski @ X2 @ X4) @ (k2_zfmisc_1 @ X3 @ X6))
% 0.20/0.46          | ~ (r2_hidden @ X4 @ X6)
% 0.20/0.46          | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((r2_hidden @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.46        (k2_zfmisc_1 @ (k2_tarski @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.46  thf(t15_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.20/0.46       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.46         (((k1_mcart_1 @ X11) = (X10))
% 0.20/0.46          | ((k1_mcart_1 @ X11) = (X12))
% 0.20/0.46          | ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ (k2_tarski @ X12 @ X10) @ X13)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((((k1_mcart_1 @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.20/0.46          = (sk_C))
% 0.20/0.46        | ((k1_mcart_1 @ 
% 0.20/0.46            (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A))) = (
% 0.20/0.46            sk_D)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf(t7_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.46      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.46        | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.46      inference('split', [status(esa)], ['14'])).
% 0.20/0.46  thf('16', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.46        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.20/0.46         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['17'])).
% 0.20/0.46  thf('19', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | 
% 0.20/0.46       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.46      inference('split', [status(esa)], ['14'])).
% 0.20/0.46  thf('21', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['15', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['17'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.20/0.46       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.46      inference('split', [status(esa)], ['17'])).
% 0.20/0.46  thf('25', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['19', '24'])).
% 0.20/0.46  thf('26', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['23', '25'])).
% 0.20/0.46  thf('27', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['13', '22', '26'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.32/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EG7C4Ef7Iw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:21 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 154 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 (1150 expanded)
%              Number of equality atoms :   15 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( r2_hidden @ X85 @ X84 )
      | ~ ( r1_tarski @ ( k2_tarski @ X83 @ X85 ) @ X84 ) ) ),
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
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( r2_hidden @ X83 @ X84 )
      | ~ ( r1_tarski @ ( k2_tarski @ X83 @ X85 ) @ X84 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X83: $i,X85: $i,X86: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X83 @ X85 ) @ X86 )
      | ~ ( r2_hidden @ X85 @ X86 )
      | ~ ( r2_hidden @ X83 @ X86 ) ) ),
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
    ! [X81: $i,X82: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X81 @ X82 ) )
      = ( k2_xboole_0 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X81: $i,X82: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X81 @ X82 ) )
      = ( k2_xboole_0 @ X81 @ X82 ) ) ),
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
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( r2_hidden @ X83 @ X84 )
      | ~ ( r1_tarski @ ( k2_tarski @ X83 @ X85 ) @ X84 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EG7C4Ef7Iw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 173 iterations in 0.120s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(t47_zfmisc_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.38/0.57       ( r2_hidden @ A @ C ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.38/0.57          ( r2_hidden @ A @ C ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.38/0.57  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X4 : $i, X6 : $i]:
% 0.38/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.57        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.57  thf(t38_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.38/0.57         ((r2_hidden @ X85 @ X84)
% 0.38/0.57          | ~ (r1_tarski @ (k2_tarski @ X83 @ X85) @ X84))),
% 0.38/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.38/0.57         ((r2_hidden @ X83 @ X84)
% 0.38/0.57          | ~ (r1_tarski @ (k2_tarski @ X83 @ X85) @ X84))),
% 0.38/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X83 : $i, X85 : $i, X86 : $i]:
% 0.38/0.57         ((r1_tarski @ (k2_tarski @ X83 @ X85) @ X86)
% 0.38/0.57          | ~ (r2_hidden @ X85 @ X86)
% 0.38/0.57          | ~ (r2_hidden @ X83 @ X86))),
% 0.38/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.57          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X4 : $i, X6 : $i]:
% 0.38/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.38/0.57          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '12'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(l51_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X81 : $i, X82 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X81 @ X82)) = (k2_xboole_0 @ X81 @ X82))),
% 0.38/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X81 : $i, X82 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X81 @ X82)) = (k2_xboole_0 @ X81 @ X82))),
% 0.38/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf(t7_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '21', '22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.38/0.57      inference('sup+', [status(thm)], ['24', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.38/0.57         ((r2_hidden @ X83 @ X84)
% 0.38/0.57          | ~ (r1_tarski @ (k2_tarski @ X83 @ X85) @ X84))),
% 0.38/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.57  thf('30', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

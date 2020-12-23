%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zm34rvts0y

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 255 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t56_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
          & ( r2_hidden @ C @ A ) )
       => ( r1_tarski @ C @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t56_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ X12 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ sk_A ),
    inference(simplify,[status(thm)],['5'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X4 ) @ ( k4_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zm34rvts0y
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 38 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(t56_setfam_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.46       ( r1_tarski @ C @ B ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.46          ( r1_tarski @ C @ B ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t56_setfam_1])).
% 0.20/0.46  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(l35_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46       ( r2_hidden @ A @ B ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X10 : $i, X12 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ (k1_tarski @ X10) @ X12) = (k1_xboole_0))
% 0.20/0.46          | ~ (r2_hidden @ X10 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(l32_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46        | (r1_tarski @ (k1_tarski @ sk_C) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ sk_A)),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf(t95_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X14) @ (k3_tarski @ X15))
% 0.20/0.46          | ~ (r1_tarski @ X14 @ X15))),
% 0.20/0.46      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((r1_tarski @ (k3_tarski @ (k1_tarski @ sk_C)) @ (k3_tarski @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf(t31_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.46  thf('9', plain, (![X13 : $i]: ((k3_tarski @ (k1_tarski @ X13)) = (X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.46  thf('10', plain, ((r1_tarski @ sk_C @ (k3_tarski @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((k4_xboole_0 @ sk_C @ (k3_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t34_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.46          | (r1_tarski @ (k4_xboole_0 @ X5 @ X4) @ (k4_xboole_0 @ X5 @ X3)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.20/0.46          (k4_xboole_0 @ X0 @ (k3_tarski @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C @ sk_B) @ k1_xboole_0)),
% 0.20/0.46      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.46  thf(t3_xboole_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.46  thf('18', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.46  thf('21', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.46  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

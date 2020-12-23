%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4EGfclLgsP

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  80 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 433 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 != X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('12',plain,(
    ! [X42: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X42 ) )
     != ( k1_tarski @ X42 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','9'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','9'])).

thf('16',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4EGfclLgsP
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 48 iterations in 0.023s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(t7_xboole_0, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.44          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.44  thf(t49_zfmisc_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i]:
% 0.20/0.44        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t7_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.44  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.20/0.44      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf(t28_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i]:
% 0.20/0.44         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.20/0.44      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf(t4_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.44            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.20/0.44          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.44          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.44  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.44  thf('8', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.20/0.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.44  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.44  thf(t20_zfmisc_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.44         ( k1_tarski @ A ) ) <=>
% 0.20/0.44       ( ( A ) != ( B ) ) ))).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X42 : $i, X43 : $i]:
% 0.20/0.44         (((X43) != (X42))
% 0.20/0.44          | ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X42))
% 0.20/0.44              != (k1_tarski @ X43)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X42 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X42))
% 0.20/0.44           != (k1_tarski @ X42))),
% 0.20/0.44      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.44  thf('14', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.44  thf('15', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.44  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.44  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.44      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.44  thf(t100_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      (![X6 : $i, X7 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X6 @ X7)
% 0.20/0.44           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.44  thf(t5_boole, axiom,
% 0.20/0.44    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.44  thf('20', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.44      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.44  thf('21', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.20/0.44  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

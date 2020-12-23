%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f2WFU1NK5b

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:48 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 187 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  489 (1643 expanded)
%              Number of equality atoms :   60 ( 181 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(demod,[status(thm)],['9','10','11','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) )
      | ( X33
        = ( k4_tarski @ ( sk_E @ X33 @ X32 @ X31 ) @ ( sk_F @ X33 @ X32 @ X31 ) ) )
      | ~ ( r2_hidden @ X33 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k2_mcart_1 @ X34 ) )
      | ( X34
       != ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k4_tarski @ X35 @ X36 )
     != ( k2_mcart_1 @ ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) )
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('28',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1','28'])).

thf('30',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_mcart_1 @ X34 ) )
      | ( X34
       != ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('33',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k4_tarski @ X35 @ X36 )
     != ( k1_mcart_1 @ ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) )
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('36',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['29','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f2WFU1NK5b
% 0.15/0.37  % Computer   : n006.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:37:23 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.55/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.76  % Solved by: fo/fo7.sh
% 0.55/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.76  % done 820 iterations in 0.280s
% 0.55/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.76  % SZS output start Refutation
% 0.55/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.76  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.55/0.76  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.55/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.76  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.55/0.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.55/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.76  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.55/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.76  thf(t67_mcart_1, conjecture,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.55/0.76       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.76        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.55/0.76          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t67_mcart_1])).
% 0.55/0.76  thf('0', plain,
% 0.55/0.76      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('1', plain,
% 0.55/0.76      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(t48_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.76  thf('3', plain,
% 0.55/0.76      (![X9 : $i, X10 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.55/0.76           = (k3_xboole_0 @ X9 @ X10))),
% 0.55/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.76  thf('4', plain,
% 0.55/0.76      (![X9 : $i, X10 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.55/0.76           = (k3_xboole_0 @ X9 @ X10))),
% 0.55/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.76  thf('5', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.76           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.76  thf(t47_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      (![X7 : $i, X8 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.55/0.76           = (k4_xboole_0 @ X7 @ X8))),
% 0.55/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.55/0.76  thf('7', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X1 @ X0)
% 0.55/0.76           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.76      inference('demod', [status(thm)], ['5', '6'])).
% 0.55/0.76  thf(t51_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.55/0.76       ( A ) ))).
% 0.55/0.76  thf('8', plain,
% 0.55/0.76      (![X11 : $i, X12 : $i]:
% 0.55/0.76         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.55/0.76           = (X11))),
% 0.55/0.76      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.55/0.76  thf('9', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.55/0.76           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 0.55/0.76      inference('sup+', [status(thm)], ['7', '8'])).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      (![X9 : $i, X10 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.55/0.76           = (k3_xboole_0 @ X9 @ X10))),
% 0.55/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.76  thf(t52_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.55/0.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.55/0.76  thf('11', plain,
% 0.55/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.55/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.55/0.76              (k3_xboole_0 @ X13 @ X15)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.55/0.76  thf(d6_xboole_0, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( k5_xboole_0 @ A @ B ) =
% 0.55/0.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.76  thf('12', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((k5_xboole_0 @ X0 @ X1)
% 0.55/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.55/0.76  thf(l36_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.55/0.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.55/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X2 @ X4)))),
% 0.55/0.76      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 0.55/0.76           = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.76      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.76  thf('15', plain,
% 0.55/0.76      (![X7 : $i, X8 : $i]:
% 0.55/0.76         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.55/0.76           = (k4_xboole_0 @ X7 @ X8))),
% 0.55/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.55/0.76  thf(t92_xboole_1, axiom,
% 0.55/0.76    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.55/0.76  thf('16', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.55/0.76      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.55/0.76  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.76      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.55/0.76  thf('18', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.55/0.76      inference('demod', [status(thm)], ['9', '10', '11', '17'])).
% 0.55/0.76  thf(t36_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.76  thf('19', plain,
% 0.55/0.76      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.55/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.76  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.76      inference('sup+', [status(thm)], ['18', '19'])).
% 0.55/0.76  thf(t103_zfmisc_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.55/0.76          ( r2_hidden @ D @ A ) & 
% 0.55/0.76          ( ![E:$i,F:$i]:
% 0.55/0.76            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.55/0.76                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.55/0.76  thf('21', plain,
% 0.55/0.76      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.76         (~ (r1_tarski @ X30 @ (k2_zfmisc_1 @ X31 @ X32))
% 0.55/0.76          | ((X33)
% 0.55/0.76              = (k4_tarski @ (sk_E @ X33 @ X32 @ X31) @ 
% 0.55/0.76                 (sk_F @ X33 @ X32 @ X31)))
% 0.55/0.76          | ~ (r2_hidden @ X33 @ X30))),
% 0.55/0.76      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.55/0.76  thf('22', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.55/0.76          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.76  thf('23', plain,
% 0.55/0.76      (((sk_A)
% 0.55/0.76         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.55/0.76            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['2', '22'])).
% 0.55/0.76  thf(t20_mcart_1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.55/0.76       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.55/0.76  thf('24', plain,
% 0.55/0.76      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.76         (((X34) != (k2_mcart_1 @ X34)) | ((X34) != (k4_tarski @ X35 @ X36)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.55/0.76  thf('25', plain,
% 0.55/0.76      (![X35 : $i, X36 : $i]:
% 0.55/0.76         ((k4_tarski @ X35 @ X36) != (k2_mcart_1 @ (k4_tarski @ X35 @ X36)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['24'])).
% 0.55/0.76  thf('26', plain,
% 0.55/0.76      (((k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ (sk_F @ sk_A @ sk_C @ sk_B))
% 0.55/0.76         != (k2_mcart_1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['23', '25'])).
% 0.55/0.76  thf('27', plain,
% 0.55/0.76      (((sk_A)
% 0.55/0.76         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.55/0.76            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['2', '22'])).
% 0.55/0.76  thf('28', plain, (((sk_A) != (k2_mcart_1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.76  thf('29', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.55/0.76      inference('simplify_reflect-', [status(thm)], ['1', '28'])).
% 0.55/0.76  thf('30', plain,
% 0.55/0.76      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('31', plain,
% 0.55/0.76      (((sk_A)
% 0.55/0.76         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.55/0.76            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['2', '22'])).
% 0.55/0.76  thf('32', plain,
% 0.55/0.76      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.76         (((X34) != (k1_mcart_1 @ X34)) | ((X34) != (k4_tarski @ X35 @ X36)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.55/0.76  thf('33', plain,
% 0.55/0.76      (![X35 : $i, X36 : $i]:
% 0.55/0.76         ((k4_tarski @ X35 @ X36) != (k1_mcart_1 @ (k4_tarski @ X35 @ X36)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['32'])).
% 0.55/0.76  thf('34', plain,
% 0.55/0.76      (((k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ (sk_F @ sk_A @ sk_C @ sk_B))
% 0.55/0.76         != (k1_mcart_1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['31', '33'])).
% 0.55/0.76  thf('35', plain,
% 0.55/0.76      (((sk_A)
% 0.55/0.76         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.55/0.76            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['2', '22'])).
% 0.55/0.76  thf('36', plain, (((sk_A) != (k1_mcart_1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['34', '35'])).
% 0.55/0.76  thf('37', plain,
% 0.55/0.76      ((((sk_A) != (sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['30', '36'])).
% 0.55/0.76  thf('38', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['37'])).
% 0.55/0.76  thf('39', plain,
% 0.55/0.76      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('40', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.55/0.76      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.55/0.76  thf('41', plain, ($false),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['29', '40'])).
% 0.55/0.76  
% 0.55/0.76  % SZS output end Refutation
% 0.55/0.76  
% 0.55/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PxpFi7flPG

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 134 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  436 (1036 expanded)
%              Number of equality atoms :   62 ( 171 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

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

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X39 @ X40 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('5',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('8',plain,(
    ! [X39: $i,X41: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X39 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) )
      = ( k1_tarski @ ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( r1_tarski @ X34 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) )
      | ( X34
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( r1_tarski @ ( k1_tarski @ X30 ) @ ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k1_tarski @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X23 ) @ X25 )
      | ~ ( r2_hidden @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('32',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('34',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) )
      = ( k1_tarski @ ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('36',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['30','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PxpFi7flPG
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 68 iterations in 0.030s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(t20_mcart_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.50          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t7_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X39 : $i, X40 : $i]: ((k1_mcart_1 @ (k4_tarski @ X39 @ X40)) = (X39))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('5', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.50  thf('7', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X39 : $i, X41 : $i]: ((k2_mcart_1 @ (k4_tarski @ X39 @ X41)) = (X41))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('9', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.22/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['1', '10'])).
% 0.22/0.50  thf(t35_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.50       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X35 : $i, X36 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X35) @ (k1_tarski @ X36))
% 0.22/0.50           = (k1_tarski @ (k4_tarski @ X35 @ X36)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.50  thf(t135_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.22/0.50         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X28 : $i, X29 : $i]:
% 0.22/0.50         (((X28) = (k1_xboole_0))
% 0.22/0.50          | ~ (r1_tarski @ X28 @ (k2_zfmisc_1 @ X29 @ X28)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t1_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.50  thf(t49_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k1_tarski @ X37) @ X38) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.50  thf('17', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.22/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '18'])).
% 0.22/0.50  thf(t69_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf(t70_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.50  thf(t142_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.22/0.50            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.22/0.50            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.22/0.50            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.22/0.50            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.22/0.50            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.22/0.50         ((r1_tarski @ X34 @ (k1_enumset1 @ X30 @ X31 @ X32))
% 0.22/0.50          | ((X34) != (k1_tarski @ X30)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.50         (r1_tarski @ (k1_tarski @ X30) @ (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.22/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.50  thf(l1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X23 : $i, X24 : $i]:
% 0.22/0.50         ((r2_hidden @ X23 @ X24) | ~ (r1_tarski @ (k1_tarski @ X23) @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '25'])).
% 0.22/0.50  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['20', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X23 : $i, X25 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X23) @ X25) | ~ (r2_hidden @ X23 @ X25))),
% 0.22/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.22/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X35 : $i, X36 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X35) @ (k1_tarski @ X36))
% 0.22/0.50           = (k1_tarski @ (k4_tarski @ X35 @ X36)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X28 : $i, X29 : $i]:
% 0.22/0.50         (((X28) = (k1_xboole_0))
% 0.22/0.50          | ~ (r1_tarski @ X28 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.22/0.50          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.22/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '39'])).
% 0.22/0.50  thf('41', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('43', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain, ($false),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['30', '43'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

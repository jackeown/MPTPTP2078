%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0NJYdNRxiX

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  332 ( 576 expanded)
%              Number of equality atoms :   54 ( 102 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X39: $i,X41: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X39 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X39 @ X40 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('12',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X38 ) )
      = ( k1_tarski @ ( k4_tarski @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['7','29'])).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X38 ) )
      = ( k1_tarski @ ( k4_tarski @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0NJYdNRxiX
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 88 iterations in 0.033s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(t20_mcart_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.48       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.48          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.19/0.48  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t7_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X39 : $i, X41 : $i]: ((k2_mcart_1 @ (k4_tarski @ X39 @ X41)) = (X41))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.19/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['2', '4'])).
% 0.19/0.48  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.19/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X39 : $i, X40 : $i]: ((k1_mcart_1 @ (k4_tarski @ X39 @ X40)) = (X39))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('10', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('12', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.19/0.48         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf(t35_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.48       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X37 : $i, X38 : $i]:
% 0.19/0.48         ((k2_zfmisc_1 @ (k1_tarski @ X37) @ (k1_tarski @ X38))
% 0.19/0.48           = (k1_tarski @ (k4_tarski @ X37 @ X38)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.19/0.48  thf(t135_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.19/0.48         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X35 : $i, X36 : $i]:
% 0.19/0.48         (((X35) = (k1_xboole_0))
% 0.19/0.48          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X35 @ X36)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.19/0.48          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.19/0.48         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.19/0.48         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.48  thf(d10_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.48  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.19/0.48         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '20'])).
% 0.19/0.48  thf(t69_enumset1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.48  thf('22', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.48  thf(fc3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X31 : $i, X32 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X31 @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.19/0.48  thf('24', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('27', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('29', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['7', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X37 : $i, X38 : $i]:
% 0.19/0.48         ((k2_zfmisc_1 @ (k1_tarski @ X37) @ (k1_tarski @ X38))
% 0.19/0.48           = (k1_tarski @ (k4_tarski @ X37 @ X38)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X35 : $i, X36 : $i]:
% 0.19/0.48         (((X35) = (k1_xboole_0))
% 0.19/0.48          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X36 @ X35)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.19/0.48          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.19/0.48        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['30', '33'])).
% 0.19/0.48  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.48  thf('36', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.48  thf('37', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('38', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('40', plain, ($false), inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

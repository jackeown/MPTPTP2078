%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3H13Ez4iXy

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  92 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  337 ( 732 expanded)
%              Number of equality atoms :   49 ( 127 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t64_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( ( k1_relat_1 @ A )
              = k1_xboole_0 )
            | ( ( k2_relat_1 @ A )
              = k1_xboole_0 ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_relat_1])).

thf('1',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r1_tarski @ sk_A @ X0 )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k4_xboole_0 @ X4 @ X6 )
       != X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r1_tarski @ sk_A @ X0 ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','8','12','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_A @ X0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('19',plain,
    ( ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','21','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','21','22'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ sk_A @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_A @ X0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k1_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['16','33'])).

thf('35',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3H13Ez4iXy
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:09:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 18 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(t21_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( r1_tarski @
% 0.20/0.46         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X10 : $i]:
% 0.20/0.46         ((r1_tarski @ X10 @ 
% 0.20/0.46           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.20/0.46          | ~ (v1_relat_1 @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.46  thf(t64_relat_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.46           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.46         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ A ) =>
% 0.20/0.46          ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.46              ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.46            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t64_relat_1])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.46        | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('split', [status(esa)], ['1'])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X10 : $i]:
% 0.20/0.46         ((r1_tarski @ X10 @ 
% 0.20/0.46           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.20/0.46          | ~ (v1_relat_1 @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.46  thf(t67_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.20/0.46         ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.46       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (((X1) = (k1_xboole_0))
% 0.20/0.46          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.46          | ~ (r1_tarski @ X1 @ X3)
% 0.20/0.46          | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (r1_xboole_0 @ 
% 0.20/0.46               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1)
% 0.20/0.46          | ~ (r1_tarski @ X0 @ X1)
% 0.20/0.46          | ((X0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((![X0 : $i]:
% 0.20/0.46          (~ (r1_xboole_0 @ 
% 0.20/0.46              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0) @ X0)
% 0.20/0.46           | ((sk_A) = (k1_xboole_0))
% 0.20/0.46           | ~ (r1_tarski @ sk_A @ X0)
% 0.20/0.46           | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.46         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.46  thf(t113_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.46  thf(t4_boole, axiom,
% 0.20/0.46    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.46  thf(t83_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ X4 @ X6) | ((k4_xboole_0 @ X4 @ X6) != (X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.46  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ X0)))
% 0.20/0.46         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '8', '12', '13'])).
% 0.20/0.46  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((![X0 : $i]: ~ (r1_tarski @ sk_A @ X0))
% 0.20/0.46         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('split', [status(esa)], ['1'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X10 : $i]:
% 0.20/0.46         ((r1_tarski @ X10 @ 
% 0.20/0.46           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.20/0.46          | ~ (v1_relat_1 @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      ((((r1_tarski @ sk_A @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_A)))
% 0.20/0.46         | ~ (v1_relat_1 @ sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.46  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (((r1_tarski @ sk_A @ k1_xboole_0))
% 0.20/0.46         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((r1_tarski @ sk_A @ k1_xboole_0))
% 0.20/0.46         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '21', '22'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (((X1) = (k1_xboole_0))
% 0.20/0.46          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.46          | ~ (r1_tarski @ X1 @ X3)
% 0.20/0.46          | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      ((![X0 : $i]:
% 0.20/0.46          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.46           | ~ (r1_tarski @ sk_A @ X0)
% 0.20/0.46           | ((sk_A) = (k1_xboole_0))))
% 0.20/0.46         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      ((![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.46         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      ((![X0 : $i]: ~ (r1_tarski @ sk_A @ X0))
% 0.20/0.46         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf('31', plain, (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['23', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.46       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('split', [status(esa)], ['1'])).
% 0.20/0.46  thf('33', plain, ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.20/0.46  thf('34', plain, (![X0 : $i]: ~ (r1_tarski @ sk_A @ X0)),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['16', '33'])).
% 0.20/0.46  thf('35', plain, (~ (v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '34'])).
% 0.20/0.46  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

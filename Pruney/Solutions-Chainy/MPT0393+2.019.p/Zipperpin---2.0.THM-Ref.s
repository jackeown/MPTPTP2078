%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1VROAtTiTA

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:43 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  96 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  435 ( 883 expanded)
%              Number of equality atoms :   59 ( 126 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ ( k1_tarski @ X26 ) )
        = X25 )
      | ( r2_hidden @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 != X21 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('3',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ X27 )
      | ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( X27
        = ( k1_setfam_1 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ X27 )
      | ( r2_hidden @ ( sk_D_1 @ X27 @ X28 ) @ X28 )
      | ( X27
        = ( k1_setfam_1 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) )
        = ( k1_tarski @ X22 ) )
      | ( X22 = X23 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ X25 @ ( k1_tarski @ X24 ) )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ ( sk_D_1 @ X27 @ X28 ) )
      | ( X27
        = ( k1_setfam_1 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['8','14'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1VROAtTiTA
% 0.13/0.31  % Computer   : n018.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 15:03:27 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.32  % Python version: Python 3.6.8
% 0.13/0.32  % Running in FO mode
% 1.22/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.22/1.41  % Solved by: fo/fo7.sh
% 1.22/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.41  % done 1399 iterations in 0.983s
% 1.22/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.22/1.41  % SZS output start Refutation
% 1.22/1.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.22/1.41  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.22/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.22/1.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.22/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.22/1.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.22/1.41  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.22/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.22/1.41  thf(t11_setfam_1, conjecture,
% 1.22/1.41    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.22/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.41    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 1.22/1.41    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 1.22/1.41  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf(t65_zfmisc_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.22/1.41       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.22/1.41  thf('1', plain,
% 1.22/1.41      (![X25 : $i, X26 : $i]:
% 1.22/1.41         (((k4_xboole_0 @ X25 @ (k1_tarski @ X26)) = (X25))
% 1.22/1.41          | (r2_hidden @ X26 @ X25))),
% 1.22/1.41      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.22/1.41  thf(t20_zfmisc_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.22/1.41         ( k1_tarski @ A ) ) <=>
% 1.22/1.41       ( ( A ) != ( B ) ) ))).
% 1.22/1.41  thf('2', plain,
% 1.22/1.41      (![X21 : $i, X22 : $i]:
% 1.22/1.41         (((X22) != (X21))
% 1.22/1.41          | ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X21))
% 1.22/1.41              != (k1_tarski @ X22)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.22/1.41  thf('3', plain,
% 1.22/1.41      (![X21 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 1.22/1.41           != (k1_tarski @ X21))),
% 1.22/1.41      inference('simplify', [status(thm)], ['2'])).
% 1.22/1.41  thf('4', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 1.22/1.41          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['1', '3'])).
% 1.22/1.41  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.22/1.41      inference('simplify', [status(thm)], ['4'])).
% 1.22/1.41  thf(d1_setfam_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 1.22/1.41         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 1.22/1.41       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.22/1.41         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 1.22/1.41           ( ![C:$i]:
% 1.22/1.41             ( ( r2_hidden @ C @ B ) <=>
% 1.22/1.41               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 1.22/1.41  thf('6', plain,
% 1.22/1.41      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.22/1.41         ((r2_hidden @ (sk_C @ X27 @ X28) @ X27)
% 1.22/1.41          | (r2_hidden @ (sk_C @ X27 @ X28) @ X29)
% 1.22/1.41          | ~ (r2_hidden @ X29 @ X28)
% 1.22/1.41          | ((X27) = (k1_setfam_1 @ X28))
% 1.22/1.41          | ((X28) = (k1_xboole_0)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d1_setfam_1])).
% 1.22/1.41  thf('7', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.22/1.41          | ((X1) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0)
% 1.22/1.41          | (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X1))),
% 1.22/1.41      inference('sup-', [status(thm)], ['5', '6'])).
% 1.22/1.41  thf('8', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.22/1.41      inference('eq_fact', [status(thm)], ['7'])).
% 1.22/1.41  thf('9', plain,
% 1.22/1.41      (![X21 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 1.22/1.41           != (k1_tarski @ X21))),
% 1.22/1.41      inference('simplify', [status(thm)], ['2'])).
% 1.22/1.41  thf(d10_xboole_0, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.22/1.41  thf('10', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.22/1.41  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.22/1.41      inference('simplify', [status(thm)], ['10'])).
% 1.22/1.41  thf(l32_xboole_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.22/1.41  thf('12', plain,
% 1.22/1.41      (![X3 : $i, X5 : $i]:
% 1.22/1.41         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.22/1.41      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.22/1.41  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.22/1.41      inference('sup-', [status(thm)], ['11', '12'])).
% 1.22/1.41  thf('14', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 1.22/1.41      inference('demod', [status(thm)], ['9', '13'])).
% 1.22/1.41  thf('15', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 1.22/1.41      inference('clc', [status(thm)], ['8', '14'])).
% 1.22/1.41  thf('16', plain,
% 1.22/1.41      (![X27 : $i, X28 : $i]:
% 1.22/1.41         (~ (r2_hidden @ (sk_C @ X27 @ X28) @ X27)
% 1.22/1.41          | (r2_hidden @ (sk_D_1 @ X27 @ X28) @ X28)
% 1.22/1.41          | ((X27) = (k1_setfam_1 @ X28))
% 1.22/1.41          | ((X28) = (k1_xboole_0)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d1_setfam_1])).
% 1.22/1.41  thf('17', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | (r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['15', '16'])).
% 1.22/1.41  thf('18', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 1.22/1.41          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['17'])).
% 1.22/1.41  thf('19', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 1.22/1.41      inference('demod', [status(thm)], ['9', '13'])).
% 1.22/1.41  thf('20', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | (r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('clc', [status(thm)], ['18', '19'])).
% 1.22/1.41  thf('21', plain,
% 1.22/1.41      (![X22 : $i, X23 : $i]:
% 1.22/1.41         (((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23))
% 1.22/1.41            = (k1_tarski @ X22))
% 1.22/1.41          | ((X22) = (X23)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.22/1.41  thf('22', plain,
% 1.22/1.41      (![X24 : $i, X25 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X24 @ X25)
% 1.22/1.41          | ((k4_xboole_0 @ X25 @ (k1_tarski @ X24)) != (X25)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.22/1.41  thf('23', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 1.22/1.41          | ((X0) = (X1))
% 1.22/1.41          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['21', '22'])).
% 1.22/1.41  thf('24', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 1.22/1.41      inference('simplify', [status(thm)], ['23'])).
% 1.22/1.41  thf('25', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | ((X0) = (sk_D_1 @ X0 @ (k1_tarski @ X0))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['20', '24'])).
% 1.22/1.41  thf('26', plain,
% 1.22/1.41      (![X27 : $i, X28 : $i]:
% 1.22/1.41         (~ (r2_hidden @ (sk_C @ X27 @ X28) @ X27)
% 1.22/1.41          | ~ (r2_hidden @ (sk_C @ X27 @ X28) @ (sk_D_1 @ X27 @ X28))
% 1.22/1.41          | ((X27) = (k1_setfam_1 @ X28))
% 1.22/1.41          | ((X28) = (k1_xboole_0)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d1_setfam_1])).
% 1.22/1.41  thf('27', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 1.22/1.41      inference('sup-', [status(thm)], ['25', '26'])).
% 1.22/1.41  thf('28', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 1.22/1.41      inference('simplify', [status(thm)], ['27'])).
% 1.22/1.41  thf('29', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 1.22/1.41      inference('demod', [status(thm)], ['9', '13'])).
% 1.22/1.41  thf('30', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.22/1.41          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 1.22/1.41      inference('clc', [status(thm)], ['28', '29'])).
% 1.22/1.41  thf('31', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.22/1.41          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 1.22/1.41      inference('clc', [status(thm)], ['8', '14'])).
% 1.22/1.41  thf('32', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('clc', [status(thm)], ['30', '31'])).
% 1.22/1.41  thf('33', plain, (((sk_A) != (sk_A))),
% 1.22/1.41      inference('demod', [status(thm)], ['0', '32'])).
% 1.22/1.41  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 1.22/1.41  
% 1.22/1.41  % SZS output end Refutation
% 1.22/1.41  
% 1.22/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AWEq8nM3Ab

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:32 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  301 ( 391 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t4_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('3',plain,(
    ! [X30: $i,X31: $i,X33: $i,X34: $i] :
      ( ( X30
       != ( k1_setfam_1 @ X31 ) )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ( r2_hidden @ X34 @ X33 )
      | ~ ( r2_hidden @ X34 @ X30 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r2_hidden @ X34 @ ( k1_setfam_1 @ X31 ) )
      | ( r2_hidden @ X34 @ X33 )
      | ~ ( r2_hidden @ X33 @ X31 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X31: $i,X36: $i] :
      ( ( X36
       != ( k1_setfam_1 @ X31 ) )
      | ( X36 = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('13',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t68_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ X29 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11','13','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AWEq8nM3Ab
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 704 iterations in 0.235s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(t4_setfam_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 0.46/0.69  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d3_tarski, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X3 : $i, X5 : $i]:
% 0.46/0.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf(d1_setfam_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.46/0.69         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.69       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.46/0.69         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.69               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (![X30 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 0.46/0.69         (((X30) != (k1_setfam_1 @ X31))
% 0.46/0.69          | ~ (r2_hidden @ X33 @ X31)
% 0.46/0.69          | (r2_hidden @ X34 @ X33)
% 0.46/0.69          | ~ (r2_hidden @ X34 @ X30)
% 0.46/0.69          | ((X31) = (k1_xboole_0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.46/0.69         (((X31) = (k1_xboole_0))
% 0.46/0.69          | ~ (r2_hidden @ X34 @ (k1_setfam_1 @ X31))
% 0.46/0.69          | (r2_hidden @ X34 @ X33)
% 0.46/0.69          | ~ (r2_hidden @ X33 @ X31))),
% 0.46/0.69      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.46/0.69          | ~ (r2_hidden @ X2 @ X0)
% 0.46/0.69          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.46/0.69          | ((X0) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['2', '4'])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (((sk_B) = (k1_xboole_0))
% 0.46/0.69          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B)) @ sk_A)
% 0.46/0.69          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '5'])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X3 : $i, X5 : $i]:
% 0.46/0.69         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)
% 0.46/0.69        | ((sk_B) = (k1_xboole_0))
% 0.46/0.69        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.46/0.69      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.69  thf('10', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.69      inference('clc', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X31 : $i, X36 : $i]:
% 0.46/0.69         (((X36) != (k1_setfam_1 @ X31))
% 0.46/0.69          | ((X36) = (k1_xboole_0))
% 0.46/0.69          | ((X31) != (k1_xboole_0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.46/0.69  thf('13', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (![X3 : $i, X5 : $i]:
% 0.46/0.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf(t68_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.69       ( r2_hidden @ A @ B ) ))).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X27 : $i, X29 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ (k1_tarski @ X27) @ X29) = (k1_xboole_0))
% 0.46/0.69          | ~ (r2_hidden @ X27 @ X29))),
% 0.46/0.69      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((r1_tarski @ X0 @ X1)
% 0.46/0.69          | ((k4_xboole_0 @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0)
% 0.46/0.69              = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.69  thf(t79_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.46/0.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      (![X3 : $i, X5 : $i]:
% 0.46/0.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X3 : $i, X5 : $i]:
% 0.46/0.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf(t3_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.69          | ~ (r2_hidden @ X8 @ X9)
% 0.46/0.69          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((r1_tarski @ X0 @ X1)
% 0.46/0.69          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.69          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((r1_tarski @ X0 @ X1)
% 0.46/0.69          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.46/0.69          | (r1_tarski @ X0 @ X1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['19', '22'])).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.46/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((r1_tarski @ k1_xboole_0 @ X1) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['18', '24'])).
% 0.46/0.69  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.69      inference('condensation', [status(thm)], ['25'])).
% 0.46/0.69  thf('27', plain, ($false),
% 0.46/0.69      inference('demod', [status(thm)], ['0', '11', '13', '26'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eg9HbSEty3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 139 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  344 ( 878 expanded)
%              Number of equality atoms :   40 (  87 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ ( sk_D @ X41 @ X42 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X43 )
      | ~ ( r1_setfam_1 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('26',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) @ k1_xboole_0 )
 != ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('32',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('33',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eg9HbSEty3
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 122 iterations in 0.039s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(t7_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.50  thf(t21_setfam_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.20/0.50  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d2_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X41 @ X42) @ X42)
% 0.20/0.50          | ~ (r2_hidden @ X41 @ X43)
% 0.20/0.50          | ~ (r1_setfam_1 @ X43 @ X42))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(l1_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X33 : $i, X35 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((r1_tarski @ (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) @ 
% 0.20/0.50        k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(t3_xboole_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('11', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t19_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.50       ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))
% 0.20/0.50           = (k1_tarski @ X36))),
% 0.20/0.50      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.50           = (k1_tarski @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t12_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X46 : $i, X47 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X0 @ X0)
% 0.20/0.50           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.50           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.50  thf(t92_xboole_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('22', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((k4_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.50         (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0))) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['10', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t20_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.50         ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ( A ) != ( B ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X38 : $i, X39 : $i]:
% 0.20/0.50         (((X39) != (X38))
% 0.20/0.50          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 0.20/0.50              != (k1_tarski @ X39)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X38 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 0.20/0.50           != (k1_tarski @ X38))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((k4_xboole_0 @ (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) @ 
% 0.20/0.50         k1_xboole_0) != (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.50  thf('34', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['26', '33'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

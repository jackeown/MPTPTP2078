%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GniP5KnbTK

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:19 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  269 ( 387 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( ( k9_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_2 @ X21 @ X19 ) ) @ X19 )
      | ( X20
       != ( k1_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('9',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_2 @ X21 @ X19 ) ) @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_D_2 @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['7','9'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X13
       != ( k9_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( r2_hidden @ X16 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X16 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ( r2_hidden @ X15 @ ( k9_relat_1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) @ ( k9_relat_1 @ sk_B_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) @ ( k9_relat_1 @ sk_B_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_2 @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) @ ( k9_relat_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,
    ( ( k9_relat_1 @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_2 @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GniP5KnbTK
% 0.15/0.38  % Computer   : n024.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:24:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 215 iterations in 0.139s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.45/0.63  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.63  thf(t7_xboole_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.63          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.63  thf(t152_relat_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.63            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.45/0.63            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i]:
% 0.45/0.63        ( ( v1_relat_1 @ B ) =>
% 0.45/0.63          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.63               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.45/0.63               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.45/0.63  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d3_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.63          | (r2_hidden @ X3 @ X5)
% 0.45/0.63          | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      ((((sk_A) = (k1_xboole_0))
% 0.45/0.63        | (r2_hidden @ (sk_B_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '4'])).
% 0.45/0.63  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('7', plain, ((r2_hidden @ (sk_B_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf(d4_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.45/0.63       ( ![C:$i]:
% 0.45/0.63         ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.63           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X21 @ X20)
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ X21 @ (sk_D_2 @ X21 @ X19)) @ X19)
% 0.45/0.63          | ((X20) != (k1_relat_1 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X19 : $i, X21 : $i]:
% 0.45/0.63         ((r2_hidden @ (k4_tarski @ X21 @ (sk_D_2 @ X21 @ X19)) @ X19)
% 0.45/0.63          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X19)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((r2_hidden @ 
% 0.45/0.63        (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_D_2 @ (sk_B_1 @ sk_A) @ sk_B_2)) @ 
% 0.45/0.63        sk_B_2)),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '9'])).
% 0.45/0.63  thf(d13_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i,C:$i]:
% 0.45/0.63         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.45/0.63           ( ![D:$i]:
% 0.45/0.63             ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.63               ( ?[E:$i]:
% 0.45/0.63                 ( ( r2_hidden @ E @ B ) & 
% 0.45/0.63                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         (((X13) != (k9_relat_1 @ X11 @ X10))
% 0.45/0.63          | (r2_hidden @ X15 @ X13)
% 0.45/0.63          | ~ (r2_hidden @ (k4_tarski @ X16 @ X15) @ X11)
% 0.45/0.63          | ~ (r2_hidden @ X16 @ X10)
% 0.45/0.63          | ~ (v1_relat_1 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X11)
% 0.45/0.63          | ~ (r2_hidden @ X16 @ X10)
% 0.45/0.63          | ~ (r2_hidden @ (k4_tarski @ X16 @ X15) @ X11)
% 0.45/0.63          | (r2_hidden @ X15 @ (k9_relat_1 @ X11 @ X10)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ (sk_D_2 @ (sk_B_1 @ sk_A) @ sk_B_2) @ 
% 0.45/0.63           (k9_relat_1 @ sk_B_2 @ X0))
% 0.45/0.63          | ~ (r2_hidden @ (sk_B_1 @ sk_A) @ X0)
% 0.45/0.63          | ~ (v1_relat_1 @ sk_B_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '12'])).
% 0.45/0.63  thf('14', plain, ((v1_relat_1 @ sk_B_2)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ (sk_D_2 @ (sk_B_1 @ sk_A) @ sk_B_2) @ 
% 0.45/0.63           (k9_relat_1 @ sk_B_2 @ X0))
% 0.45/0.63          | ~ (r2_hidden @ (sk_B_1 @ sk_A) @ X0))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((((sk_A) = (k1_xboole_0))
% 0.45/0.63        | (r2_hidden @ (sk_D_2 @ (sk_B_1 @ sk_A) @ sk_B_2) @ 
% 0.45/0.63           (k9_relat_1 @ sk_B_2 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '15'])).
% 0.45/0.63  thf('17', plain, (((k9_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      ((((sk_A) = (k1_xboole_0))
% 0.45/0.63        | (r2_hidden @ (sk_D_2 @ (sk_B_1 @ sk_A) @ sk_B_2) @ k1_xboole_0))),
% 0.45/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((r2_hidden @ (sk_D_2 @ (sk_B_1 @ sk_A) @ sk_B_2) @ k1_xboole_0)),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf(d1_xboole_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('22', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.63  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.63  thf('24', plain, ($false), inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

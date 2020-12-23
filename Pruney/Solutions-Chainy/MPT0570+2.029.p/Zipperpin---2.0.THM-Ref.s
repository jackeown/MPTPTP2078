%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ekW3Xk1h0G

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:11 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   47 (  65 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  272 ( 461 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('3',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ekW3Xk1h0G
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:30:06 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 40 iterations in 0.022s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.24/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.50  thf(d5_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.24/0.50       ( ![D:$i]:
% 0.24/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.24/0.50         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.24/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.24/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.24/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.24/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.50  thf('1', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.24/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.50  thf(t55_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.24/0.50         (~ (r1_xboole_0 @ (k2_tarski @ X16 @ X17) @ X18)
% 0.24/0.50          | ~ (r2_hidden @ X16 @ X18))),
% 0.24/0.50      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.24/0.50  thf('3', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.24/0.50          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.24/0.50  thf(t4_boole, axiom,
% 0.24/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.24/0.50          | ((X1) = (k1_xboole_0)))),
% 0.24/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.24/0.50          | ((X1) = (k1_xboole_0)))),
% 0.24/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.50  thf(t174_relat_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.50            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.24/0.50            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i]:
% 0.24/0.50        ( ( v1_relat_1 @ B ) =>
% 0.24/0.50          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.50               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.24/0.50               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.24/0.50  thf('8', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(d3_tarski, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.50          | (r2_hidden @ X0 @ X2)
% 0.24/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (((sk_A) = (k1_xboole_0))
% 0.24/0.50          | (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k2_relat_1 @ sk_B)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.24/0.50  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k2_relat_1 @ sk_B))),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf(t3_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X12 @ X10)
% 0.24/0.50          | ~ (r2_hidden @ X12 @ X13)
% 0.24/0.50          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ X1)
% 0.24/0.50          | ~ (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1))),
% 0.24/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      ((((sk_A) = (k1_xboole_0)) | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '15'])).
% 0.24/0.50  thf('17', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t173_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.50         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (![X19 : $i, X20 : $i]:
% 0.24/0.50         (((k10_relat_1 @ X19 @ X20) != (k1_xboole_0))
% 0.24/0.50          | (r1_xboole_0 @ (k2_relat_1 @ X19) @ X20)
% 0.24/0.50          | ~ (v1_relat_1 @ X19))),
% 0.24/0.50      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.24/0.50  thf('19', plain,
% 0.24/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.24/0.50        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.50  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('21', plain,
% 0.24/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.50        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.24/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.24/0.50  thf('22', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.24/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.24/0.50  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.50      inference('demod', [status(thm)], ['16', '22'])).
% 0.24/0.50  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('25', plain, ($false),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

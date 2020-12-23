%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HwGhuMSFpl

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  154 ( 184 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t35_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t35_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('2',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X8 )
      | ( X9
        = ( k1_funct_1 @ X8 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HwGhuMSFpl
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 21 iterations in 0.023s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(t35_funct_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49          ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t35_funct_1])).
% 0.21/0.49  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d10_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.49         ( ![C:$i,D:$i]:
% 0.21/0.49           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.49             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.49         (((X0) != (k6_relat_1 @ X1))
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X4) @ X0)
% 0.21/0.49          | ((X2) != (X4))
% 0.21/0.49          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X1 : $i, X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X1)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.49  thf(fc3_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('3', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X1 : $i, X4 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X4 @ X1)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ (k6_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.49  thf(t8_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.49           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X8)
% 0.21/0.49          | ((X9) = (k1_funct_1 @ X8 @ X7))
% 0.21/0.49          | ~ (v1_funct_1 @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.49        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.49        | ((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('9', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('10', plain, (((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.49  thf('11', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) != (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

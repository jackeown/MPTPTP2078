%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wVUIfRfai5

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  388 ( 593 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k3_relat_1 @ X21 ) @ ( k3_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wVUIfRfai5
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 127 iterations in 0.101s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.37/0.56  thf(d4_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.56       ( ![D:$i]:
% 0.37/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.37/0.56         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.37/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['0'])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.56          | (r2_hidden @ X4 @ X2)
% 0.37/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X1 @ X0)
% 0.37/0.56            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.37/0.56          | (r2_hidden @ 
% 0.37/0.56             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.37/0.56             X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['0'])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.37/0.56         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['0'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.37/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X1 @ X0)
% 0.37/0.56            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.37/0.56          | ((k3_xboole_0 @ X1 @ X0)
% 0.37/0.56              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ X1 @ X0)
% 0.37/0.56           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.56  thf(t17_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.37/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.56  thf(t31_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( v1_relat_1 @ B ) =>
% 0.37/0.56           ( ( r1_tarski @ A @ B ) =>
% 0.37/0.56             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X20)
% 0.37/0.56          | (r1_tarski @ (k3_relat_1 @ X21) @ (k3_relat_1 @ X20))
% 0.37/0.56          | ~ (r1_tarski @ X21 @ X20)
% 0.37/0.56          | ~ (v1_relat_1 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.37/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.56             (k3_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf(fc1_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.56             (k3_relat_1 @ X0)))),
% 0.37/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.37/0.56           (k3_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['12', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.56             (k3_relat_1 @ X0)))),
% 0.37/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf(t19_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.37/0.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X8 @ X9)
% 0.37/0.56          | ~ (r1_tarski @ X8 @ X10)
% 0.37/0.56          | (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.56             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.37/0.56          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.37/0.56             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.37/0.56          | ~ (v1_relat_1 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.56  thf(t34_relat_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( v1_relat_1 @ B ) =>
% 0.37/0.56           ( r1_tarski @
% 0.37/0.56             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.37/0.56             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( v1_relat_1 @ A ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( v1_relat_1 @ B ) =>
% 0.37/0.56              ( r1_tarski @
% 0.37/0.56                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.37/0.56                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.37/0.56          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('27', plain, ($false),
% 0.37/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

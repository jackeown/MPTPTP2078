%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VBrvI3dOnB

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:37 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   49 (  73 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 ( 878 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X5 @ X2 ) @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t115_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) )
      | ( r2_hidden @ X7 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t115_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X2 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X7 @ ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t115_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ X2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X0 ) @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X10 @ X11 ) ) @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k8_relat_1 @ X13 @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t126_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t126_relat_1])).

thf('28',plain,(
    ( k8_relat_1 @ ( k2_relat_1 @ sk_A ) @ sk_A )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VBrvI3dOnB
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 110 iterations in 0.151s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.41/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(d5_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.41/0.59       ( ![C:$i]:
% 0.41/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.41/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (![X2 : $i, X5 : $i]:
% 0.41/0.59         (((X5) = (k2_relat_1 @ X2))
% 0.41/0.59          | (r2_hidden @ (k4_tarski @ (sk_D @ X5 @ X2) @ (sk_C @ X5 @ X2)) @ X2)
% 0.41/0.59          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.41/0.59          | (r2_hidden @ X1 @ X3)
% 0.41/0.59          | ((X3) != (k2_relat_1 @ X2)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.41/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.41/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.41/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.41/0.59          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '2'])).
% 0.41/0.59  thf(t115_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ C ) =>
% 0.41/0.59       ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.41/0.59         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X7 @ (k2_relat_1 @ (k8_relat_1 @ X8 @ X9)))
% 0.41/0.59          | (r2_hidden @ X7 @ (k2_relat_1 @ X9))
% 0.41/0.59          | ~ (v1_relat_1 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t115_relat_1])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2) @ 
% 0.41/0.59           (k2_relat_1 @ X2))
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X2))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | (r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2) @ 
% 0.41/0.59             (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59           (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('eq_fact', [status(thm)], ['5'])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59           (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('eq_fact', [status(thm)], ['5'])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X7 @ X8)
% 0.41/0.59          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X9))
% 0.41/0.59          | (r2_hidden @ X7 @ (k2_relat_1 @ (k8_relat_1 @ X8 @ X9)))
% 0.41/0.59          | ~ (v1_relat_1 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t115_relat_1])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | (r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59             (k2_relat_1 @ (k8_relat_1 @ X2 @ X0)))
% 0.41/0.59          | ~ (r2_hidden @ 
% 0.41/0.59               (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ X2))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59             X2)
% 0.41/0.59          | (r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59             (k2_relat_1 @ (k8_relat_1 @ X2 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | (r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59             (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59           (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59           (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('eq_fact', [status(thm)], ['5'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X4 @ X3)
% 0.41/0.59          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.41/0.59          | ((X3) != (k2_relat_1 @ X2)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X2 : $i, X4 : $i]:
% 0.41/0.59         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.41/0.59          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | (r2_hidden @ 
% 0.41/0.59             (k4_tarski @ 
% 0.41/0.59              (sk_D_1 @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59               X0) @ 
% 0.41/0.59              (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0)) @ 
% 0.41/0.59             X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['13', '15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.41/0.59         (((X5) = (k2_relat_1 @ X2))
% 0.41/0.59          | ~ (r2_hidden @ (k4_tarski @ X6 @ (sk_C @ X5 @ X2)) @ X2)
% 0.41/0.59          | ~ (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (r2_hidden @ 
% 0.41/0.59               (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59               (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ 
% 0.41/0.59             (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 0.41/0.59            = (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 0.41/0.59              = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '19'])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 0.41/0.59              = (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.59  thf(t116_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X10 @ X11)) @ X10)
% 0.41/0.59          | ~ (v1_relat_1 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X0)
% 0.41/0.59          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.59  thf(t125_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.41/0.59         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.41/0.59          | ((k8_relat_1 @ X13 @ X12) = (X12))
% 0.41/0.59          | ~ (v1_relat_1 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.41/0.59  thf(t126_relat_1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( v1_relat_1 @ A ) =>
% 0.41/0.59          ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t126_relat_1])).
% 0.41/0.59  thf('28', plain, (((k8_relat_1 @ (k2_relat_1 @ sk_A) @ sk_A) != (sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('29', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('31', plain, (((sk_A) != (sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.59  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

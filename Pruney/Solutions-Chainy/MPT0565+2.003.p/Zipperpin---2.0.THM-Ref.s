%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CoMubDDEnr

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:41 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   41 (  72 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  505 ( 984 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ ( sk_D @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('5',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ ( sk_D @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X17 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_4 @ X17 @ X15 @ X16 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_D_4 @ X0 @ ( k2_relat_1 @ X0 ) @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_D_4 @ X0 @ ( k2_relat_1 @ X0 ) @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) ) @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ X6 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t169_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
          = ( k1_relat_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_relat_1])).

thf('21',plain,(
    ( k10_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CoMubDDEnr
% 0.15/0.37  % Computer   : n024.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:27:36 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 91 iterations in 0.132s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.42/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.42/0.61  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(d4_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.42/0.61       ( ![C:$i]:
% 0.42/0.61         ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.61           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X2 : $i, X5 : $i]:
% 0.42/0.61         (((X5) = (k1_relat_1 @ X2))
% 0.42/0.61          | (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ (sk_D @ X5 @ X2)) @ X2)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.42/0.61  thf(d5_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.42/0.61       ( ![C:$i]:
% 0.42/0.61         ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.61           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.61         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.42/0.61          | (r2_hidden @ X8 @ X10)
% 0.42/0.61          | ((X10) != (k2_relat_1 @ X9)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.61         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.42/0.61          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.42/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '2'])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '2'])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X2 : $i, X5 : $i]:
% 0.42/0.61         (((X5) = (k1_relat_1 @ X2))
% 0.42/0.61          | (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ (sk_D @ X5 @ X2)) @ X2)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.42/0.61  thf(t166_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ C ) =>
% 0.42/0.61       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.42/0.61         ( ?[D:$i]:
% 0.42/0.61           ( ( r2_hidden @ D @ B ) & 
% 0.42/0.61             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.42/0.61             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X14 @ X15)
% 0.42/0.61          | ~ (r2_hidden @ (k4_tarski @ X16 @ X14) @ X17)
% 0.42/0.61          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X17))
% 0.42/0.61          | (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.42/0.61          | ~ (v1_relat_1 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k10_relat_1 @ X0 @ X2))
% 0.42/0.61          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.61          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k10_relat_1 @ X0 @ X2))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k10_relat_1 @ X0 @ X2))
% 0.42/0.61          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.42/0.61             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '9'])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.42/0.61             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.42/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ 
% 0.42/0.61             (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.42/0.61             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('eq_fact', [status(thm)], ['11'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.42/0.61          | (r2_hidden @ (k4_tarski @ X16 @ (sk_D_4 @ X17 @ X15 @ X16)) @ X17)
% 0.42/0.61          | ~ (v1_relat_1 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | (r2_hidden @ 
% 0.42/0.61             (k4_tarski @ 
% 0.42/0.61              (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.42/0.61              (sk_D_4 @ X0 @ (k2_relat_1 @ X0) @ 
% 0.42/0.61               (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0))) @ 
% 0.42/0.61             X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ 
% 0.42/0.61           (k4_tarski @ (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.42/0.61            (sk_D_4 @ X0 @ (k2_relat_1 @ X0) @ 
% 0.42/0.61             (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0))) @ 
% 0.42/0.61           X0)
% 0.42/0.61          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.42/0.61         (((X5) = (k1_relat_1 @ X2))
% 0.42/0.61          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ X6) @ X2)
% 0.42/0.61          | ~ (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (r2_hidden @ 
% 0.42/0.61               (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.42/0.61               (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.42/0.61          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ 
% 0.42/0.61             (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.42/0.61             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.42/0.61          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.42/0.61          | (r2_hidden @ 
% 0.42/0.61             (sk_C @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.42/0.61             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('eq_fact', [status(thm)], ['11'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('clc', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf(t169_relat_1, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ A ) =>
% 0.42/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( v1_relat_1 @ A ) =>
% 0.42/0.61          ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t169_relat_1])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (((k10_relat_1 @ sk_A @ (k2_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('24', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3eESXErUep

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
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

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X9 ) @ ( sk_C_1 @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('5',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X9 ) @ ( sk_C_1 @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X17 @ X15 @ X16 ) @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X12
        = ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_C_1 @ X12 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t146_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
          = ( k2_relat_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_relat_1])).

thf('21',plain,(
    ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3eESXErUep
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 91 iterations in 0.136s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.59  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.37/0.59  thf(d5_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.37/0.59       ( ![C:$i]:
% 0.37/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (![X9 : $i, X12 : $i]:
% 0.37/0.59         (((X12) = (k2_relat_1 @ X9))
% 0.37/0.59          | (r2_hidden @ 
% 0.37/0.59             (k4_tarski @ (sk_D_2 @ X12 @ X9) @ (sk_C_1 @ X12 @ X9)) @ X9)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.37/0.59  thf(d4_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.37/0.59       ( ![C:$i]:
% 0.37/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.37/0.59          | (r2_hidden @ X0 @ X3)
% 0.37/0.59          | ((X3) != (k1_relat_1 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.37/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.37/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ (sk_D_2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '2'])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ (sk_D_2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['0', '2'])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X9 : $i, X12 : $i]:
% 0.37/0.59         (((X12) = (k2_relat_1 @ X9))
% 0.37/0.59          | (r2_hidden @ 
% 0.37/0.59             (k4_tarski @ (sk_D_2 @ X12 @ X9) @ (sk_C_1 @ X12 @ X9)) @ X9)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.37/0.59  thf(t143_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ C ) =>
% 0.37/0.59       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.37/0.59         ( ?[D:$i]:
% 0.37/0.59           ( ( r2_hidden @ D @ B ) & 
% 0.37/0.59             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.37/0.59             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X14 @ X15)
% 0.37/0.59          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X17)
% 0.37/0.59          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X17))
% 0.37/0.59          | (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.37/0.59          | ~ (v1_relat_1 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k9_relat_1 @ X0 @ X2))
% 0.37/0.59          | ~ (r2_hidden @ (sk_D_2 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.59          | ~ (r2_hidden @ (sk_D_2 @ X1 @ X0) @ X2))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         (((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ~ (r2_hidden @ (sk_D_2 @ X1 @ X0) @ X2)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k9_relat_1 @ X0 @ X2))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k9_relat_1 @ X0 @ X2))
% 0.37/0.59          | ~ (r2_hidden @ (sk_D_2 @ X1 @ X0) @ X2)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ 
% 0.37/0.59             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['3', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ 
% 0.37/0.59             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.59          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.37/0.59          | ((X1) = (k2_relat_1 @ X0)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ 
% 0.37/0.59             (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.37/0.59             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('eq_fact', [status(thm)], ['11'])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.37/0.59          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X17 @ X15 @ X16) @ X16) @ X17)
% 0.37/0.59          | ~ (v1_relat_1 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | (r2_hidden @ 
% 0.37/0.59             (k4_tarski @ 
% 0.37/0.59              (sk_D_4 @ X0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.59               (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.37/0.59              (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.37/0.59             X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r2_hidden @ 
% 0.37/0.59           (k4_tarski @ 
% 0.37/0.59            (sk_D_4 @ X0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.59             (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.37/0.59            (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.37/0.59           X0)
% 0.37/0.59          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (![X9 : $i, X12 : $i, X13 : $i]:
% 0.37/0.59         (((X12) = (k2_relat_1 @ X9))
% 0.37/0.59          | ~ (r2_hidden @ (k4_tarski @ X13 @ (sk_C_1 @ X12 @ X9)) @ X9)
% 0.37/0.59          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.37/0.59          | ~ (r2_hidden @ 
% 0.37/0.59               (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.37/0.59               (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.59          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (r2_hidden @ 
% 0.37/0.59             (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.37/0.59             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.59          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.37/0.59          | (r2_hidden @ 
% 0.37/0.59             (sk_C_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.37/0.59             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('eq_fact', [status(thm)], ['11'])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.37/0.59      inference('clc', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf(t146_relat_1, conjecture,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) =>
% 0.37/0.59       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i]:
% 0.37/0.59        ( ( v1_relat_1 @ A ) =>
% 0.37/0.59          ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t146_relat_1])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.59  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('24', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.59  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

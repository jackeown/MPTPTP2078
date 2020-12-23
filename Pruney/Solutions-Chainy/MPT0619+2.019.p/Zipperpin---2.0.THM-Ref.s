%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nCBSUG6ToZ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 147 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  511 (1580 expanded)
%              Number of equality atoms :   47 ( 171 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k11_relat_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ( X19
        = ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ ( k11_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('41',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nCBSUG6ToZ
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 79 iterations in 0.047s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(d1_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X0 : $i, X4 : $i]:
% 0.19/0.49         (((X4) = (k1_tarski @ X0))
% 0.19/0.49          | ((sk_C @ X4 @ X0) = (X0))
% 0.19/0.49          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.49  thf(t146_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X13 : $i]:
% 0.19/0.49         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.19/0.49          | ~ (v1_relat_1 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.19/0.49  thf(t14_funct_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.49       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.19/0.49         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.49          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.19/0.49            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.19/0.49  thf('2', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d16_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.19/0.49          | ~ (v1_relat_1 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_B)
% 0.19/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['1', '4'])).
% 0.19/0.49  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.49  thf(t204_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.49         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X14 @ (k11_relat_1 @ X15 @ X16))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X16 @ X14) @ X15)
% 0.19/0.49          | ~ (v1_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.19/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.19/0.49          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k4_tarski @ sk_A @ (sk_C @ (k2_relat_1 @ sk_B) @ X0)) @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '12'])).
% 0.19/0.49  thf(t8_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.49           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         (~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.19/0.49          | ((X19) = (k1_funct_1 @ X18 @ X17))
% 0.19/0.49          | ~ (v1_funct_1 @ X18)
% 0.19/0.49          | ~ (v1_relat_1 @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.19/0.49          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.19/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.19/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.19/0.49          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.19/0.49          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.19/0.49          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.19/0.49          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.19/0.49          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.19/0.49      inference('eq_fact', [status(thm)], ['18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.49        | ((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.19/0.49            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.19/0.49         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X0 : $i, X4 : $i]:
% 0.19/0.49         (((X4) = (k1_tarski @ X0))
% 0.19/0.49          | ((sk_C @ X4 @ X0) != (X0))
% 0.19/0.49          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.19/0.49        | ((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.19/0.49            != (k1_funct_1 @ sk_B @ sk_A))
% 0.19/0.49        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.49  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.49  thf('28', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['25', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.19/0.49          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.19/0.49          | ~ (v1_funct_1 @ X18)
% 0.19/0.49          | ~ (v1_relat_1 @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X18)
% 0.19/0.49          | ~ (v1_funct_1 @ X18)
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.19/0.49          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.19/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '30'])).
% 0.19/0.49  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.49         (~ (r2_hidden @ (k4_tarski @ X16 @ X14) @ X15)
% 0.19/0.49          | (r2_hidden @ X14 @ (k11_relat_1 @ X15 @ X16))
% 0.19/0.49          | ~ (v1_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.49        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('38', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.19/0.49         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 0.19/0.49        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '39', '40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('44', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

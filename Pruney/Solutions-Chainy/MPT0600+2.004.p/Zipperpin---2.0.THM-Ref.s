%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yLmr0hfKHk

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  98 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  545 ( 961 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t204_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t204_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k11_relat_1 @ X5 @ X6 )
        = ( k9_relat_1 @ X5 @ ( k1_tarski @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['8','9','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k11_relat_1 @ X5 @ X6 )
        = ( k9_relat_1 @ X5 @ ( k1_tarski @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k11_relat_1 @ X5 @ X6 )
        = ( k9_relat_1 @ X5 @ ( k1_tarski @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('39',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( sk_D @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yLmr0hfKHk
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 59 iterations in 0.052s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(t204_relat_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ C ) =>
% 0.20/0.51          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51            ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t204_relat_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.51       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(d16_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((k11_relat_1 @ X5 @ X6) = (k9_relat_1 @ X5 @ (k1_tarski @ X6)))
% 0.20/0.51          | ~ (v1_relat_1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf(t143_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.51         ( ?[D:$i]:
% 0.20/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X10)
% 0.20/0.51          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X10))
% 0.20/0.51          | (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v1_relat_1 @ sk_C_1)
% 0.20/0.51           | (r2_hidden @ sk_B @ (k9_relat_1 @ sk_C_1 @ X0))
% 0.20/0.51           | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.20/0.51           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf(t20_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.51           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 0.20/0.51          | (r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C_1 @ X0))
% 0.20/0.51           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '16'])).
% 0.20/0.51  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.51       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((k11_relat_1 @ X5 @ X6) = (k9_relat_1 @ X5 @ (k1_tarski @ X6)))
% 0.20/0.51          | ~ (v1_relat_1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ X10 @ X8 @ X9) @ X9) @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ 
% 0.20/0.51           (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.51         | (r2_hidden @ 
% 0.20/0.51            (k4_tarski @ (sk_D @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.20/0.51            sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.51  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((k11_relat_1 @ X5 @ X6) = (k9_relat_1 @ X5 @ (k1_tarski @ X6)))
% 0.20/0.51          | ~ (v1_relat_1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ X8)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.51         | (r2_hidden @ (sk_D @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.20/0.51            (k1_tarski @ sk_A))))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '34'])).
% 0.20/0.51  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.20/0.51         (k1_tarski @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X0 : $i, X3 : $i]:
% 0.20/0.51         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((sk_D @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) = (sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.51         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '21', '22', '43'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

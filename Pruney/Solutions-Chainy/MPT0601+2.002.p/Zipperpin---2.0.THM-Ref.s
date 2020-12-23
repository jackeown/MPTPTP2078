%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MRSDRlCNeV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:41 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   61 (  90 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  495 ( 795 expanded)
%              Number of equality atoms :   34 (  58 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k11_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k11_relat_1 @ X18 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MRSDRlCNeV
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 133 iterations in 0.104s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(t205_relat_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.39/0.57         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i]:
% 0.39/0.57        ( ( v1_relat_1 @ B ) =>
% 0.39/0.57          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.39/0.57            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.39/0.57        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.39/0.57       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.39/0.57         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.39/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('split', [status(esa)], ['3'])).
% 0.39/0.57  thf(d4_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]:
% 0.39/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.57           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X14 @ X13)
% 0.39/0.57          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.39/0.57          | ((X13) != (k1_relat_1 @ X12)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X12 : $i, X14 : $i]:
% 0.39/0.57         ((r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.39/0.57          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.57  thf(t204_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.39/0.57         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         (~ (r2_hidden @ (k4_tarski @ X19 @ X17) @ X18)
% 0.39/0.57          | (r2_hidden @ X17 @ (k11_relat_1 @ X18 @ X19))
% 0.39/0.57          | ~ (v1_relat_1 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.39/0.57         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.39/0.57            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.39/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['2', '11'])).
% 0.39/0.57  thf(t7_xboole_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.57  thf(t1_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.39/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         ((r2_hidden @ X2 @ X3)
% 0.39/0.57          | (r2_hidden @ X2 @ X4)
% 0.39/0.57          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k5_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.57          | (r2_hidden @ (sk_B @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 0.39/0.57          | (r2_hidden @ (sk_B @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ (sk_B @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 0.39/0.57          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('eq_fact', [status(thm)], ['15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.39/0.57          | ~ (r2_hidden @ X2 @ X4)
% 0.39/0.57          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k5_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.57          | ~ (r2_hidden @ (sk_B @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 0.39/0.57          | ~ (r2_hidden @ (sk_B @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.39/0.57          | ~ (r2_hidden @ (sk_B @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 0.39/0.57          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r2_hidden @ (sk_B @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 0.39/0.57          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ (sk_B @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 0.39/0.57          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('eq_fact', [status(thm)], ['15'])).
% 0.39/0.57  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('clc', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.39/0.57          | ~ (r2_hidden @ X2 @ X4)
% 0.39/0.57          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.39/0.57          | ~ (r2_hidden @ X1 @ X0)
% 0.39/0.57          | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.57  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.57      inference('condensation', [status(thm)], ['26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.39/0.57       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.39/0.57       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['3'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X17 @ (k11_relat_1 @ X18 @ X19))
% 0.39/0.57          | (r2_hidden @ (k4_tarski @ X19 @ X17) @ X18)
% 0.39/0.57          | ~ (v1_relat_1 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.39/0.57             X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.39/0.57          | (r2_hidden @ X10 @ X13)
% 0.39/0.57          | ((X13) != (k1_relat_1 @ X12)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.57         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.39/0.57          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.39/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.39/0.57          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.39/0.57         | ~ (v1_relat_1 @ sk_B_1)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.39/0.57         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.57      inference('split', [status(esa)], ['3'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.39/0.57         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.39/0.57             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.39/0.57       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.57  thf('43', plain, ($false),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['1', '28', '29', '42'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

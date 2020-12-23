%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b9Ppgwv9Uy

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:46 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 143 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  449 (1115 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('10',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
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

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('21',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ ( k11_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','13'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['16','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k11_relat_1 @ X17 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['16','31','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['33','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b9Ppgwv9Uy
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 143 iterations in 0.117s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(l13_xboole_0, axiom,
% 0.39/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf(t205_relat_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ B ) =>
% 0.39/0.59       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.39/0.59         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i]:
% 0.39/0.59        ( ( v1_relat_1 @ B ) =>
% 0.39/0.59          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.39/0.59            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.39/0.59        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.39/0.59         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['3'])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          (((X0) != (k1_xboole_0))
% 0.39/0.59           | ~ (v1_xboole_0 @ X0)
% 0.39/0.59           | ~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.39/0.59         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '4'])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))
% 0.39/0.59         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.39/0.59         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.59  thf('7', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.59  thf(d1_xboole_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf(t3_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X6 @ X4)
% 0.39/0.59          | ~ (r2_hidden @ X6 @ X7)
% 0.39/0.59          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ X0)
% 0.39/0.59          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.39/0.59          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.59  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.39/0.59         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('demod', [status(thm)], ['6', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.39/0.59       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.59      inference('split', [status(esa)], ['3'])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.39/0.59        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.39/0.59         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['17'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.39/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.59      inference('split', [status(esa)], ['3'])).
% 0.39/0.59  thf(d4_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.39/0.59       ( ![C:$i]:
% 0.39/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X13 @ X12)
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.39/0.59          | ((X12) != (k1_relat_1 @ X11)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X11 : $i, X13 : $i]:
% 0.39/0.59         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.39/0.59          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.39/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['19', '21'])).
% 0.39/0.59  thf(t204_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ C ) =>
% 0.39/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.39/0.59         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         (~ (r2_hidden @ (k4_tarski @ X18 @ X16) @ X17)
% 0.39/0.59          | (r2_hidden @ X16 @ (k11_relat_1 @ X17 @ X18))
% 0.39/0.59          | ~ (v1_relat_1 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (((~ (v1_relat_1 @ sk_B_1)
% 0.39/0.59         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.39/0.59            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.39/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.39/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.39/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.39/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.39/0.59             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '28'])).
% 0.39/0.59  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '13'])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.39/0.59       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['16', '31'])).
% 0.39/0.59  thf('33', plain, (~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['15', '32'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X16 @ (k11_relat_1 @ X17 @ X18))
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X18 @ X16) @ X17)
% 0.39/0.59          | ~ (v1_relat_1 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ (k11_relat_1 @ X1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X1)
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.39/0.59             X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.59         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.39/0.59          | (r2_hidden @ X9 @ X12)
% 0.39/0.59          | ((X12) != (k1_relat_1 @ X11)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.59         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.39/0.59          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.39/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_xboole_0 @ (k11_relat_1 @ X0 @ X1))
% 0.39/0.59          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['36', '38'])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.39/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.39/0.59      inference('split', [status(esa)], ['17'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.39/0.59       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('split', [status(esa)], ['17'])).
% 0.39/0.59  thf('42', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['16', '31', '41'])).
% 0.39/0.59  thf('43', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (((v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['39', '43'])).
% 0.39/0.59  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('46', plain, ((v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.59  thf('47', plain, ($false), inference('demod', [status(thm)], ['33', '46'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

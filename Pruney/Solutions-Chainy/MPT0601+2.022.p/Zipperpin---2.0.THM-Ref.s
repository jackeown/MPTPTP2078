%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2KABQYlPCl

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  416 ( 606 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k11_relat_1 @ X9 @ X10 )
        = ( k9_relat_1 @ X9 @ ( k1_tarski @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k9_relat_1 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X7 )
      | ~ ( r2_hidden @ X5 @ ( k4_xboole_0 @ X6 @ ( k1_tarski @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X6 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','17'])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k11_relat_1 @ X21 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X11 @ X14 )
      | ( X14
       != ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2KABQYlPCl
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 57 iterations in 0.038s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(t205_relat_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ B ) =>
% 0.22/0.50          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.50            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.50        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.50       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.22/0.50        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf(d16_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (((k11_relat_1 @ X9 @ X10) = (k9_relat_1 @ X9 @ (k1_tarski @ X10)))
% 0.22/0.50          | ~ (v1_relat_1 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.50  thf(t151_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i]:
% 0.22/0.50         (((k9_relat_1 @ X18 @ X19) != (k1_xboole_0))
% 0.22/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.22/0.50          | ~ (v1_relat_1 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.50         | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.22/0.50  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A)))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf(t83_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_xboole_0 @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.22/0.50          = (k1_relat_1 @ sk_B_1)))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t64_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (((X5) != (X7))
% 0.22/0.50          | ~ (r2_hidden @ X5 @ (k4_xboole_0 @ X6 @ (k1_tarski @ X7))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X6 @ (k1_tarski @ X7)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.50       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf(t7_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.50  thf(t204_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X20 @ (k11_relat_1 @ X21 @ X22))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X22 @ X20) @ X21)
% 0.22/0.50          | ~ (v1_relat_1 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.22/0.50             X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf(d4_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 0.22/0.50          | (r2_hidden @ X11 @ X14)
% 0.22/0.50          | ((X14) != (k1_relat_1 @ X13)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         ((r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 0.22/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.50         | ~ (v1_relat_1 @ sk_B_1)))
% 0.22/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.50             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.50  thf('33', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '32'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

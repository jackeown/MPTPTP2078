%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CmB7HBbceH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:23 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   17
%              Number of atoms          :  505 ( 618 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k1_wellord1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_wellord1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_wellord1 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_wellord1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( X9
       != ( k1_wellord1 @ X8 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X7 ) @ X8 )
      | ( X11 = X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( X11 = X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X7 ) @ X8 )
      | ( r2_hidden @ X11 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X0 @ X2 ) @ X1 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X0 @ X2 ) @ X1 ) ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X0 @ X2 ) @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X0 @ X2 ) @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X0 @ X2 ) @ X1 ) ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X0 @ X2 ) @ X1 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) @ X0 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( ( sk_C @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) @ X0 ) @ ( k1_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) @ X0 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X0 @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t21_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) @ ( k1_wellord1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) @ ( k1_wellord1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_wellord1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_A ) @ sk_B ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k1_wellord1 @ X8 @ X7 ) )
      | ( X10 != X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CmB7HBbceH
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.19/1.38  % Solved by: fo/fo7.sh
% 1.19/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.38  % done 286 iterations in 0.927s
% 1.19/1.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.19/1.38  % SZS output start Refutation
% 1.19/1.38  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 1.19/1.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.19/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.38  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 1.19/1.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.19/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.38  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.19/1.38  thf(dt_k2_wellord1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 1.19/1.38  thf('0', plain,
% 1.19/1.38      (![X14 : $i, X15 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k2_wellord1 @ X14 @ X15)))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.19/1.38  thf('1', plain,
% 1.19/1.38      (![X14 : $i, X15 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k2_wellord1 @ X14 @ X15)))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.19/1.38  thf(d3_tarski, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( r1_tarski @ A @ B ) <=>
% 1.19/1.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.19/1.38  thf('2', plain,
% 1.19/1.38      (![X1 : $i, X3 : $i]:
% 1.19/1.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.19/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.19/1.38  thf(d1_wellord1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) =>
% 1.19/1.38       ( ![B:$i,C:$i]:
% 1.19/1.38         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 1.19/1.38           ( ![D:$i]:
% 1.19/1.38             ( ( r2_hidden @ D @ C ) <=>
% 1.19/1.38               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 1.19/1.38  thf('3', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.19/1.38         (((X9) != (k1_wellord1 @ X8 @ X7))
% 1.19/1.38          | (r2_hidden @ (k4_tarski @ X10 @ X7) @ X8)
% 1.19/1.38          | ~ (r2_hidden @ X10 @ X9)
% 1.19/1.38          | ~ (v1_relat_1 @ X8))),
% 1.19/1.38      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.19/1.38  thf('4', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X8)
% 1.19/1.38          | ~ (r2_hidden @ X10 @ (k1_wellord1 @ X8 @ X7))
% 1.19/1.38          | (r2_hidden @ (k4_tarski @ X10 @ X7) @ X8))),
% 1.19/1.38      inference('simplify', [status(thm)], ['3'])).
% 1.19/1.38  thf('5', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.19/1.38          | (r2_hidden @ 
% 1.19/1.38             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.19/1.38          | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['2', '4'])).
% 1.19/1.38  thf(d6_wellord1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( k2_wellord1 @ A @ B ) =
% 1.19/1.38           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 1.19/1.38  thf('6', plain,
% 1.19/1.38      (![X12 : $i, X13 : $i]:
% 1.19/1.38         (((k2_wellord1 @ X12 @ X13)
% 1.19/1.38            = (k3_xboole_0 @ X12 @ (k2_zfmisc_1 @ X13 @ X13)))
% 1.19/1.38          | ~ (v1_relat_1 @ X12))),
% 1.19/1.38      inference('cnf', [status(esa)], [d6_wellord1])).
% 1.19/1.38  thf(t17_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.38  thf('7', plain,
% 1.19/1.38      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 1.19/1.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.38  thf('8', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_tarski @ (k2_wellord1 @ X1 @ X0) @ X1) | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['6', '7'])).
% 1.19/1.38  thf('9', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (~ (r2_hidden @ X0 @ X1)
% 1.19/1.38          | (r2_hidden @ X0 @ X2)
% 1.19/1.38          | ~ (r1_tarski @ X1 @ X2))),
% 1.19/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.19/1.38  thf('10', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X0)
% 1.19/1.38          | (r2_hidden @ X2 @ X0)
% 1.19/1.38          | ~ (r2_hidden @ X2 @ (k2_wellord1 @ X0 @ X1)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['8', '9'])).
% 1.19/1.38  thf('11', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0))
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2) @ X3)
% 1.19/1.38          | (r2_hidden @ 
% 1.19/1.38             (k4_tarski @ 
% 1.19/1.38              (sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2)) @ X2) @ 
% 1.19/1.38             X1)
% 1.19/1.38          | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['5', '10'])).
% 1.19/1.38  thf('12', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X1)
% 1.19/1.38          | ~ (v1_relat_1 @ X1)
% 1.19/1.38          | (r2_hidden @ 
% 1.19/1.38             (k4_tarski @ 
% 1.19/1.38              (sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2)) @ X2) @ 
% 1.19/1.38             X1)
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2) @ X3))),
% 1.19/1.38      inference('sup-', [status(thm)], ['1', '11'])).
% 1.19/1.38  thf('13', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         ((r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2) @ X3)
% 1.19/1.38          | (r2_hidden @ 
% 1.19/1.38             (k4_tarski @ 
% 1.19/1.38              (sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2)) @ X2) @ 
% 1.19/1.38             X1)
% 1.19/1.38          | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('simplify', [status(thm)], ['12'])).
% 1.19/1.38  thf('14', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 1.19/1.38         (((X9) != (k1_wellord1 @ X8 @ X7))
% 1.19/1.38          | (r2_hidden @ X11 @ X9)
% 1.19/1.38          | ~ (r2_hidden @ (k4_tarski @ X11 @ X7) @ X8)
% 1.19/1.38          | ((X11) = (X7))
% 1.19/1.38          | ~ (v1_relat_1 @ X8))),
% 1.19/1.38      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.19/1.38  thf('15', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X8)
% 1.19/1.38          | ((X11) = (X7))
% 1.19/1.38          | ~ (r2_hidden @ (k4_tarski @ X11 @ X7) @ X8)
% 1.19/1.38          | (r2_hidden @ X11 @ (k1_wellord1 @ X8 @ X7)))),
% 1.19/1.38      inference('simplify', [status(thm)], ['14'])).
% 1.19/1.38  thf('16', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X0)
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X0 @ X2) @ X1) @ X3)
% 1.19/1.38          | (r2_hidden @ 
% 1.19/1.38             (sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X0 @ X2) @ X1)) @ 
% 1.19/1.38             (k1_wellord1 @ X0 @ X1))
% 1.19/1.38          | ((sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X0 @ X2) @ X1)) = (X1))
% 1.19/1.38          | ~ (v1_relat_1 @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['13', '15'])).
% 1.19/1.38  thf('17', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (((sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X0 @ X2) @ X1)) = (X1))
% 1.19/1.38          | (r2_hidden @ 
% 1.19/1.38             (sk_C @ X3 @ (k1_wellord1 @ (k2_wellord1 @ X0 @ X2) @ X1)) @ 
% 1.19/1.38             (k1_wellord1 @ X0 @ X1))
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X0 @ X2) @ X1) @ X3)
% 1.19/1.38          | ~ (v1_relat_1 @ X0))),
% 1.19/1.38      inference('simplify', [status(thm)], ['16'])).
% 1.19/1.38  thf('18', plain,
% 1.19/1.38      (![X1 : $i, X3 : $i]:
% 1.19/1.38         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.19/1.38  thf('19', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X1)
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X2) @ X0) @ 
% 1.19/1.38             (k1_wellord1 @ X1 @ X0))
% 1.19/1.38          | ((sk_C @ (k1_wellord1 @ X1 @ X0) @ 
% 1.19/1.38              (k1_wellord1 @ (k2_wellord1 @ X1 @ X2) @ X0)) = (X0))
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X2) @ X0) @ 
% 1.19/1.38             (k1_wellord1 @ X1 @ X0)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['17', '18'])).
% 1.19/1.38  thf('20', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (((sk_C @ (k1_wellord1 @ X1 @ X0) @ 
% 1.19/1.38            (k1_wellord1 @ (k2_wellord1 @ X1 @ X2) @ X0)) = (X0))
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X2) @ X0) @ 
% 1.19/1.38             (k1_wellord1 @ X1 @ X0))
% 1.19/1.38          | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('simplify', [status(thm)], ['19'])).
% 1.19/1.38  thf('21', plain,
% 1.19/1.38      (![X1 : $i, X3 : $i]:
% 1.19/1.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.19/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.19/1.38  thf('22', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         ((r2_hidden @ X0 @ (k1_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0))
% 1.19/1.38          | ~ (v1_relat_1 @ X2)
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0) @ 
% 1.19/1.38             (k1_wellord1 @ X2 @ X0))
% 1.19/1.38          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0) @ 
% 1.19/1.38             (k1_wellord1 @ X2 @ X0)))),
% 1.19/1.38      inference('sup+', [status(thm)], ['20', '21'])).
% 1.19/1.38  thf('23', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         ((r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0) @ 
% 1.19/1.38           (k1_wellord1 @ X2 @ X0))
% 1.19/1.38          | ~ (v1_relat_1 @ X2)
% 1.19/1.38          | (r2_hidden @ X0 @ (k1_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)))),
% 1.19/1.38      inference('simplify', [status(thm)], ['22'])).
% 1.19/1.38  thf(t21_wellord1, conjecture,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ C ) =>
% 1.19/1.38       ( r1_tarski @
% 1.19/1.38         ( k1_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) @ 
% 1.19/1.38         ( k1_wellord1 @ C @ B ) ) ))).
% 1.19/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.38    (~( ![A:$i,B:$i,C:$i]:
% 1.19/1.38        ( ( v1_relat_1 @ C ) =>
% 1.19/1.38          ( r1_tarski @
% 1.19/1.38            ( k1_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) @ 
% 1.19/1.38            ( k1_wellord1 @ C @ B ) ) ) )),
% 1.19/1.38    inference('cnf.neg', [status(esa)], [t21_wellord1])).
% 1.19/1.38  thf('24', plain,
% 1.19/1.38      (~ (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_A) @ sk_B) @ 
% 1.19/1.38          (k1_wellord1 @ sk_C_1 @ sk_B))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('25', plain,
% 1.19/1.38      (((r2_hidden @ sk_B @ 
% 1.19/1.38         (k1_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_A) @ sk_B))
% 1.19/1.38        | ~ (v1_relat_1 @ sk_C_1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['23', '24'])).
% 1.19/1.38  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('27', plain,
% 1.19/1.38      ((r2_hidden @ sk_B @ (k1_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_A) @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['25', '26'])).
% 1.19/1.38  thf('28', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.19/1.38         (((X9) != (k1_wellord1 @ X8 @ X7))
% 1.19/1.38          | ((X10) != (X7))
% 1.19/1.38          | ~ (r2_hidden @ X10 @ X9)
% 1.19/1.38          | ~ (v1_relat_1 @ X8))),
% 1.19/1.38      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.19/1.38  thf('29', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 1.19/1.38      inference('simplify', [status(thm)], ['28'])).
% 1.19/1.38  thf('30', plain, (~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.19/1.38      inference('sup-', [status(thm)], ['27', '29'])).
% 1.19/1.38  thf('31', plain, (~ (v1_relat_1 @ sk_C_1)),
% 1.19/1.38      inference('sup-', [status(thm)], ['0', '30'])).
% 1.19/1.38  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('33', plain, ($false), inference('demod', [status(thm)], ['31', '32'])).
% 1.19/1.38  
% 1.19/1.38  % SZS output end Refutation
% 1.19/1.38  
% 1.19/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

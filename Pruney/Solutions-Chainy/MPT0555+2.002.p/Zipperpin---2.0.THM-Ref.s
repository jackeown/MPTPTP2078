%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kAAJN0spXE

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :  310 ( 522 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t157_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t106_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k7_relat_1 @ X6 @ X7 ) @ ( k7_relat_1 @ X5 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t106_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_B @ X1 ) @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_B @ X1 ) @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_B @ X0 ) @ ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kAAJN0spXE
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 101 iterations in 0.092s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(t157_relat_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ C ) =>
% 0.20/0.54           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.54             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( v1_relat_1 @ B ) =>
% 0.20/0.54          ( ![C:$i]:
% 0.20/0.54            ( ( v1_relat_1 @ C ) =>
% 0.20/0.54              ( ( r1_tarski @ B @ C ) =>
% 0.20/0.54                ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t157_relat_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t148_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf(dt_k7_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.54  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t106_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ D ) =>
% 0.20/0.54           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.20/0.54             ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X5)
% 0.20/0.54          | (r1_tarski @ (k7_relat_1 @ X6 @ X7) @ (k7_relat_1 @ X5 @ X8))
% 0.20/0.54          | ~ (r1_tarski @ X6 @ X5)
% 0.20/0.54          | ~ (r1_tarski @ X7 @ X8)
% 0.20/0.54          | ~ (v1_relat_1 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t106_relat_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ sk_B)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X0)
% 0.20/0.54          | (r1_tarski @ (k7_relat_1 @ sk_B @ X1) @ (k7_relat_1 @ sk_C @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.54          | (r1_tarski @ (k7_relat_1 @ sk_B @ X1) @ (k7_relat_1 @ sk_C @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (r1_tarski @ (k7_relat_1 @ sk_B @ X0) @ (k7_relat_1 @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '12'])).
% 0.20/0.54  thf(t25_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ B ) =>
% 0.20/0.54           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.54             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.54               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X11)
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 0.20/0.54          | ~ (r1_tarski @ X12 @ X11)
% 0.20/0.54          | ~ (v1_relat_1 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.54             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ sk_B)
% 0.20/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.54             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.54  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.54             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ sk_C)
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.54             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '18'])).
% 0.20/0.54  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.54          (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 0.20/0.54           (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['2', '21'])).
% 0.20/0.54  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 0.20/0.54          (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k9_relat_1 @ sk_C @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '24'])).
% 0.20/0.54  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

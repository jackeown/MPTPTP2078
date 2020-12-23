%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Atqv87u4Wc

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:09 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   67 (  77 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  357 ( 470 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_zfmisc_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X8 ) ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['22','26','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['10','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Atqv87u4Wc
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.61  % Solved by: fo/fo7.sh
% 0.34/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.61  % done 342 iterations in 0.147s
% 0.34/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.61  % SZS output start Refutation
% 0.34/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.34/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.34/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.61  thf(t8_boole, axiom,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.34/0.61  thf('0', plain,
% 0.34/0.61      (![X15 : $i, X16 : $i]:
% 0.34/0.61         (~ (v1_xboole_0 @ X15) | ~ (v1_xboole_0 @ X16) | ((X15) = (X16)))),
% 0.34/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.34/0.61  thf(t174_relat_1, conjecture,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ( v1_relat_1 @ B ) =>
% 0.34/0.61       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.61            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.34/0.61            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.34/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.61    (~( ![A:$i,B:$i]:
% 0.34/0.61        ( ( v1_relat_1 @ B ) =>
% 0.34/0.61          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.61               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.34/0.61               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.34/0.61    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.34/0.61  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.61  thf('2', plain,
% 0.34/0.61      (![X0 : $i]:
% 0.34/0.61         (((sk_A) != (X0))
% 0.34/0.61          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.34/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.34/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.61  thf(d1_xboole_0, axiom,
% 0.34/0.61    (![A:$i]:
% 0.34/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.34/0.61  thf('3', plain,
% 0.34/0.61      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.34/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.34/0.61  thf(t113_zfmisc_1, axiom,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.61  thf('4', plain,
% 0.34/0.61      (![X20 : $i, X21 : $i]:
% 0.34/0.61         (((k2_zfmisc_1 @ X20 @ X21) = (k1_xboole_0))
% 0.34/0.61          | ((X21) != (k1_xboole_0)))),
% 0.34/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.34/0.61  thf('5', plain,
% 0.34/0.61      (![X20 : $i]: ((k2_zfmisc_1 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.34/0.61  thf(t152_zfmisc_1, axiom,
% 0.34/0.61    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.34/0.61  thf('6', plain,
% 0.34/0.61      (![X22 : $i, X23 : $i]: ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.34/0.61      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.34/0.61  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.61  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.61      inference('sup-', [status(thm)], ['3', '7'])).
% 0.34/0.61  thf('9', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.61      inference('demod', [status(thm)], ['2', '8'])).
% 0.34/0.61  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.34/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.34/0.61  thf('11', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.34/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.61  thf(t173_relat_1, axiom,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ( v1_relat_1 @ B ) =>
% 0.34/0.61       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.61         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.61  thf('12', plain,
% 0.34/0.61      (![X26 : $i, X27 : $i]:
% 0.34/0.61         (((k10_relat_1 @ X26 @ X27) != (k1_xboole_0))
% 0.34/0.61          | (r1_xboole_0 @ (k2_relat_1 @ X26) @ X27)
% 0.34/0.61          | ~ (v1_relat_1 @ X26))),
% 0.34/0.61      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.34/0.61  thf('13', plain,
% 0.34/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.61        | ~ (v1_relat_1 @ sk_B_1)
% 0.34/0.61        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.34/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.61  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.34/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.61  thf('15', plain,
% 0.34/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.61        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.34/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.34/0.61  thf('16', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.34/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.34/0.61  thf('17', plain,
% 0.34/0.61      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.34/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.34/0.61  thf(t4_xboole_0, axiom,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.34/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.34/0.61  thf('18', plain,
% 0.34/0.61      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.34/0.61          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.34/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.34/0.61  thf(t12_setfam_1, axiom,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.61  thf('19', plain,
% 0.34/0.61      (![X24 : $i, X25 : $i]:
% 0.34/0.61         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.34/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.61  thf('20', plain,
% 0.34/0.61      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X7 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X8)))
% 0.34/0.61          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.34/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.61  thf('21', plain,
% 0.34/0.61      (![X0 : $i, X1 : $i]:
% 0.34/0.61         ((v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.34/0.61          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.34/0.61      inference('sup-', [status(thm)], ['17', '20'])).
% 0.34/0.61  thf('22', plain,
% 0.34/0.61      ((v1_xboole_0 @ 
% 0.34/0.61        (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['16', '21'])).
% 0.34/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.34/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.34/0.62  thf('23', plain,
% 0.34/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.34/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.34/0.62  thf('24', plain,
% 0.34/0.62      (![X24 : $i, X25 : $i]:
% 0.34/0.62         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.34/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.62  thf('25', plain,
% 0.34/0.62      (![X24 : $i, X25 : $i]:
% 0.34/0.62         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.34/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.62  thf('26', plain,
% 0.34/0.62      (![X0 : $i, X1 : $i]:
% 0.34/0.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.34/0.62           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.34/0.62      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.34/0.62  thf('27', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf(l32_xboole_1, axiom,
% 0.34/0.62    (![A:$i,B:$i]:
% 0.34/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.62  thf('28', plain,
% 0.34/0.62      (![X9 : $i, X11 : $i]:
% 0.34/0.62         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.34/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.62  thf('29', plain,
% 0.34/0.62      (((k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.34/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.62  thf(t48_xboole_1, axiom,
% 0.34/0.62    (![A:$i,B:$i]:
% 0.34/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.62  thf('30', plain,
% 0.34/0.62      (![X13 : $i, X14 : $i]:
% 0.34/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.34/0.62           = (k3_xboole_0 @ X13 @ X14))),
% 0.34/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.34/0.62  thf('31', plain,
% 0.34/0.62      (![X24 : $i, X25 : $i]:
% 0.34/0.62         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.34/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.62  thf('32', plain,
% 0.34/0.62      (![X13 : $i, X14 : $i]:
% 0.34/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.34/0.62           = (k1_setfam_1 @ (k2_tarski @ X13 @ X14)))),
% 0.34/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.34/0.62  thf('33', plain,
% 0.34/0.62      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.34/0.62         = (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.34/0.62      inference('sup+', [status(thm)], ['29', '32'])).
% 0.34/0.62  thf(t3_boole, axiom,
% 0.34/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.62  thf('34', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.34/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.34/0.62  thf('35', plain,
% 0.34/0.62      (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.34/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.34/0.62  thf('36', plain, ((v1_xboole_0 @ sk_A)),
% 0.34/0.62      inference('demod', [status(thm)], ['22', '26', '35'])).
% 0.34/0.62  thf('37', plain, ($false), inference('demod', [status(thm)], ['10', '36'])).
% 0.34/0.62  
% 0.34/0.62  % SZS output end Refutation
% 0.34/0.62  
% 0.34/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

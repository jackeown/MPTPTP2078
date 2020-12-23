%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xXe2fHGD2Z

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 ( 478 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X3 ) @ ( k1_relat_1 @ X2 ) )
      | ( v5_funct_1 @ X2 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X7 ) )
      | ( ( k10_relat_1 @ X7 @ ( k1_tarski @ X8 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xXe2fHGD2Z
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:14:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.42  % Solved by: fo/fo7.sh
% 0.19/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.42  % done 22 iterations in 0.008s
% 0.19/0.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.42  % SZS output start Refutation
% 0.19/0.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.42  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.42  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.42  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.42  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.42  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.19/0.42  thf(t60_relat_1, axiom,
% 0.19/0.42    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.42     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.42  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.42      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.42  thf(d20_funct_1, axiom,
% 0.19/0.42    (![A:$i]:
% 0.19/0.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.42       ( ![B:$i]:
% 0.19/0.42         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.42           ( ( v5_funct_1 @ B @ A ) <=>
% 0.19/0.42             ( ![C:$i]:
% 0.19/0.42               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.42                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.42  thf('1', plain,
% 0.19/0.42      (![X2 : $i, X3 : $i]:
% 0.19/0.42         (~ (v1_relat_1 @ X2)
% 0.19/0.42          | ~ (v1_funct_1 @ X2)
% 0.19/0.42          | (r2_hidden @ (sk_C @ X2 @ X3) @ (k1_relat_1 @ X2))
% 0.19/0.42          | (v5_funct_1 @ X2 @ X3)
% 0.19/0.42          | ~ (v1_funct_1 @ X3)
% 0.19/0.42          | ~ (v1_relat_1 @ X3))),
% 0.19/0.42      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.19/0.42  thf('2', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ X0)
% 0.19/0.42          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.42      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.42  thf(t174_funct_1, conjecture,
% 0.19/0.42    (![A:$i]:
% 0.19/0.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.42       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.19/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.42    (~( ![A:$i]:
% 0.19/0.42        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.42          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.19/0.42    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.19/0.42  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf(t110_relat_1, axiom,
% 0.19/0.42    (![A:$i]:
% 0.19/0.42     ( ( v1_relat_1 @ A ) =>
% 0.19/0.42       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.42  thf('4', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.42          | ~ (v1_relat_1 @ X0))),
% 0.19/0.42      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.19/0.42  thf(fc8_funct_1, axiom,
% 0.19/0.42    (![A:$i,B:$i]:
% 0.19/0.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.42       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.19/0.42         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.19/0.42  thf('5', plain,
% 0.19/0.42      (![X5 : $i, X6 : $i]:
% 0.19/0.42         (~ (v1_funct_1 @ X5)
% 0.19/0.42          | ~ (v1_relat_1 @ X5)
% 0.19/0.42          | (v1_funct_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.19/0.42      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.19/0.42  thf('6', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         ((v1_funct_1 @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ X0))),
% 0.19/0.42      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.42  thf('7', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         (~ (v1_funct_1 @ X0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | (v1_funct_1 @ k1_xboole_0))),
% 0.19/0.42      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.42  thf('8', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_A))),
% 0.19/0.42      inference('sup-', [status(thm)], ['3', '7'])).
% 0.19/0.42  thf('9', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf('10', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.42      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.42  thf('11', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ X0)
% 0.19/0.42          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.42          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.42      inference('demod', [status(thm)], ['2', '10'])).
% 0.19/0.42  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf('13', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.42          | ~ (v1_relat_1 @ X0))),
% 0.19/0.42      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.19/0.42  thf('14', plain,
% 0.19/0.42      (![X5 : $i, X6 : $i]:
% 0.19/0.42         (~ (v1_funct_1 @ X5)
% 0.19/0.42          | ~ (v1_relat_1 @ X5)
% 0.19/0.42          | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.19/0.42      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.19/0.42  thf('15', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         ((v1_relat_1 @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ X0))),
% 0.19/0.42      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.42  thf('16', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         (~ (v1_funct_1 @ X0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.42      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.42  thf('17', plain, (((v1_relat_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_A))),
% 0.19/0.42      inference('sup-', [status(thm)], ['12', '16'])).
% 0.19/0.42  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.42      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.42  thf('20', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ X0)
% 0.19/0.42          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.19/0.42      inference('demod', [status(thm)], ['11', '19'])).
% 0.19/0.42  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.42      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.42  thf(t142_funct_1, axiom,
% 0.19/0.42    (![A:$i,B:$i]:
% 0.19/0.42     ( ( v1_relat_1 @ B ) =>
% 0.19/0.42       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.19/0.42         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.42  thf('22', plain,
% 0.19/0.42      (![X7 : $i, X8 : $i]:
% 0.19/0.42         (~ (r2_hidden @ X8 @ (k2_relat_1 @ X7))
% 0.19/0.42          | ((k10_relat_1 @ X7 @ (k1_tarski @ X8)) != (k1_xboole_0))
% 0.19/0.42          | ~ (v1_relat_1 @ X7))),
% 0.19/0.42      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.19/0.42  thf('23', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.42          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.42          | ((k10_relat_1 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_xboole_0)))),
% 0.19/0.42      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.42  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.42      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.42  thf(t172_relat_1, axiom,
% 0.19/0.42    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.42  thf('25', plain,
% 0.19/0.42      (![X1 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.19/0.42      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.19/0.42  thf('26', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.42      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.42  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.42      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.42  thf('28', plain,
% 0.19/0.42      (![X0 : $i]:
% 0.19/0.42         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.42          | ~ (v1_funct_1 @ X0)
% 0.19/0.42          | ~ (v1_relat_1 @ X0))),
% 0.19/0.42      inference('sup-', [status(thm)], ['20', '27'])).
% 0.19/0.42  thf('29', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf('30', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.19/0.42      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.42  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.42  thf('33', plain, ($false),
% 0.19/0.42      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.19/0.42  
% 0.19/0.42  % SZS output end Refutation
% 0.19/0.42  
% 0.19/0.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

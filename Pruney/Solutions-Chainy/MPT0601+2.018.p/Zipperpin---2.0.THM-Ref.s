%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u3yzOKNWsY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  419 ( 631 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ ( k11_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k9_relat_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u3yzOKNWsY
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 66 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t205_relat_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.48         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ B ) =>
% 0.20/0.48          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.48            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.20/0.48        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(d4_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.20/0.48          | ((X16) != (k1_relat_1 @ X15)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X15 : $i, X17 : $i]:
% 0.20/0.48         ((r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.20/0.48          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.48  thf(t204_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.48         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.48         (~ (r2_hidden @ (k4_tarski @ X24 @ X22) @ X23)
% 0.20/0.48          | (r2_hidden @ X22 @ (k11_relat_1 @ X23 @ X24))
% 0.20/0.48          | ~ (v1_relat_1 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ sk_B)
% 0.20/0.48         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.20/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '11'])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(t4_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.48          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.48  thf('16', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.48  thf('17', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(d16_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.48  thf(l27_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k1_tarski @ X9) @ X10) | (r2_hidden @ X9 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf(t151_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X20) @ X21)
% 0.20/0.48          | ((k9_relat_1 @ X20 @ X21) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k9_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '29'])).
% 0.20/0.48  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.48             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.48  thf('36', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '35'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

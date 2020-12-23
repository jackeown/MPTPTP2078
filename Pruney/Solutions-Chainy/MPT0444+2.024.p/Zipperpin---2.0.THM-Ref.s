%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KyOQgHKPHY

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:48 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  330 ( 665 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_D @ X12 @ X13 ) ) @ X13 )
      | ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_D @ X12 @ X13 ) ) @ X12 )
      | ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KyOQgHKPHY
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.55  % Solved by: fo/fo7.sh
% 1.36/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.55  % done 1191 iterations in 1.096s
% 1.36/1.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.55  % SZS output start Refutation
% 1.36/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.36/1.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.36/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.36/1.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.36/1.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.36/1.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.55  thf(commutativity_k3_xboole_0, axiom,
% 1.36/1.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.36/1.55  thf('0', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.55  thf(t48_xboole_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.36/1.55  thf('1', plain,
% 1.36/1.55      (![X8 : $i, X9 : $i]:
% 1.36/1.55         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.36/1.55           = (k3_xboole_0 @ X8 @ X9))),
% 1.36/1.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.55  thf(fc2_relat_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 1.36/1.55  thf('2', plain,
% 1.36/1.55      (![X17 : $i, X18 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k4_xboole_0 @ X17 @ X18)))),
% 1.36/1.55      inference('cnf', [status(esa)], [fc2_relat_1])).
% 1.36/1.55  thf('3', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 1.36/1.55      inference('sup+', [status(thm)], ['1', '2'])).
% 1.36/1.55  thf(d3_relat_1, axiom,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( v1_relat_1 @ A ) =>
% 1.36/1.55       ( ![B:$i]:
% 1.36/1.55         ( ( r1_tarski @ A @ B ) <=>
% 1.36/1.55           ( ![C:$i,D:$i]:
% 1.36/1.55             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 1.36/1.55               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 1.36/1.55  thf('4', plain,
% 1.36/1.55      (![X12 : $i, X13 : $i]:
% 1.36/1.55         ((r2_hidden @ (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_D @ X12 @ X13)) @ 
% 1.36/1.55           X13)
% 1.36/1.55          | (r1_tarski @ X13 @ X12)
% 1.36/1.55          | ~ (v1_relat_1 @ X13))),
% 1.36/1.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.36/1.55  thf('5', plain,
% 1.36/1.55      (![X12 : $i, X13 : $i]:
% 1.36/1.55         (~ (r2_hidden @ 
% 1.36/1.55             (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_D @ X12 @ X13)) @ X12)
% 1.36/1.55          | (r1_tarski @ X13 @ X12)
% 1.36/1.55          | ~ (v1_relat_1 @ X13))),
% 1.36/1.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.36/1.55  thf('6', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X0)
% 1.36/1.55          | (r1_tarski @ X0 @ X0)
% 1.36/1.55          | ~ (v1_relat_1 @ X0)
% 1.36/1.55          | (r1_tarski @ X0 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['4', '5'])).
% 1.36/1.55  thf('7', plain, (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ~ (v1_relat_1 @ X0))),
% 1.36/1.55      inference('simplify', [status(thm)], ['6'])).
% 1.36/1.55  thf(t18_xboole_1, axiom,
% 1.36/1.55    (![A:$i,B:$i,C:$i]:
% 1.36/1.55     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.36/1.55  thf('8', plain,
% 1.36/1.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.36/1.55         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.36/1.55      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.36/1.55  thf('9', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.36/1.55          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.36/1.55      inference('sup-', [status(thm)], ['7', '8'])).
% 1.36/1.55  thf('10', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.36/1.55      inference('sup-', [status(thm)], ['3', '9'])).
% 1.36/1.55  thf(t25_relat_1, axiom,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( v1_relat_1 @ A ) =>
% 1.36/1.55       ( ![B:$i]:
% 1.36/1.55         ( ( v1_relat_1 @ B ) =>
% 1.36/1.55           ( ( r1_tarski @ A @ B ) =>
% 1.36/1.55             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.36/1.55               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.36/1.55  thf('11', plain,
% 1.36/1.55      (![X19 : $i, X20 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X19)
% 1.36/1.55          | (r1_tarski @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19))
% 1.36/1.55          | ~ (r1_tarski @ X20 @ X19)
% 1.36/1.55          | ~ (v1_relat_1 @ X20))),
% 1.36/1.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.36/1.55  thf('12', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X0)
% 1.36/1.55          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.36/1.55          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.36/1.55             (k2_relat_1 @ X0))
% 1.36/1.55          | ~ (v1_relat_1 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['10', '11'])).
% 1.36/1.55  thf('13', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.36/1.55           (k2_relat_1 @ X0))
% 1.36/1.55          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.36/1.55          | ~ (v1_relat_1 @ X0))),
% 1.36/1.55      inference('simplify', [status(thm)], ['12'])).
% 1.36/1.55  thf('14', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 1.36/1.55      inference('sup+', [status(thm)], ['1', '2'])).
% 1.36/1.55  thf('15', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X0)
% 1.36/1.55          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.36/1.55             (k2_relat_1 @ X0)))),
% 1.36/1.55      inference('clc', [status(thm)], ['13', '14'])).
% 1.36/1.55  thf('16', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.36/1.55           (k2_relat_1 @ X0))
% 1.36/1.55          | ~ (v1_relat_1 @ X0))),
% 1.36/1.55      inference('sup+', [status(thm)], ['0', '15'])).
% 1.36/1.55  thf('17', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X0)
% 1.36/1.55          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.36/1.55             (k2_relat_1 @ X0)))),
% 1.36/1.55      inference('clc', [status(thm)], ['13', '14'])).
% 1.36/1.55  thf(t19_xboole_1, axiom,
% 1.36/1.55    (![A:$i,B:$i,C:$i]:
% 1.36/1.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.36/1.55       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.36/1.55  thf('18', plain,
% 1.36/1.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.55         (~ (r1_tarski @ X5 @ X6)
% 1.36/1.55          | ~ (r1_tarski @ X5 @ X7)
% 1.36/1.55          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.36/1.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.36/1.55  thf('19', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X0)
% 1.36/1.55          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.36/1.55             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 1.36/1.55          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 1.36/1.55      inference('sup-', [status(thm)], ['17', '18'])).
% 1.36/1.55  thf('20', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (v1_relat_1 @ X0)
% 1.36/1.55          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.36/1.55             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 1.36/1.55          | ~ (v1_relat_1 @ X1))),
% 1.36/1.55      inference('sup-', [status(thm)], ['16', '19'])).
% 1.36/1.55  thf(t27_relat_1, conjecture,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( v1_relat_1 @ A ) =>
% 1.36/1.55       ( ![B:$i]:
% 1.36/1.55         ( ( v1_relat_1 @ B ) =>
% 1.36/1.55           ( r1_tarski @
% 1.36/1.55             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.36/1.55             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.36/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.55    (~( ![A:$i]:
% 1.36/1.55        ( ( v1_relat_1 @ A ) =>
% 1.36/1.55          ( ![B:$i]:
% 1.36/1.55            ( ( v1_relat_1 @ B ) =>
% 1.36/1.55              ( r1_tarski @
% 1.36/1.55                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.36/1.55                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 1.36/1.55    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 1.36/1.55  thf('21', plain,
% 1.36/1.55      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.36/1.55          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('22', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.36/1.55      inference('sup-', [status(thm)], ['20', '21'])).
% 1.36/1.55  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('25', plain, ($false),
% 1.36/1.55      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.36/1.55  
% 1.36/1.55  % SZS output end Refutation
% 1.36/1.55  
% 1.36/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

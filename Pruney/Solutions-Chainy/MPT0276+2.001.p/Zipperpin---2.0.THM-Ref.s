%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zkATiRlYpJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:38 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :  339 ( 805 expanded)
%              Number of equality atoms :   30 (  83 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X18 @ X20 ) @ X21 )
        = ( k2_tarski @ X18 @ X20 ) )
      | ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t74_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != k1_xboole_0 )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k1_tarski @ A ) )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k1_tarski @ B ) )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != k1_xboole_0 )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k1_tarski @ A ) )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k1_tarski @ B ) )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_zfmisc_1])).

thf('2',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X10 @ X12 ) @ X13 )
        = ( k1_tarski @ X10 ) )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C )
      | ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ sk_C )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X10 @ X12 ) @ X13 )
        = ( k1_tarski @ X10 ) )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_C )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['8'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('21',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zkATiRlYpJ
% 0.14/0.37  % Computer   : n006.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:44:53 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 154 iterations in 0.064s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(commutativity_k2_tarski, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.54  thf(t72_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.37/0.54       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k2_tarski @ X18 @ X20) @ X21)
% 0.37/0.54            = (k2_tarski @ X18 @ X20))
% 0.37/0.54          | (r2_hidden @ X20 @ X21)
% 0.37/0.54          | (r2_hidden @ X18 @ X21))),
% 0.37/0.54      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.37/0.54  thf(t74_zfmisc_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ~( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ A ) ) & 
% 0.37/0.54          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ B ) ) & 
% 0.37/0.54          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) !=
% 0.37/0.54            ( k2_tarski @ A @ B ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.54        ( ~( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ A ) ) & 
% 0.37/0.54             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ B ) ) & 
% 0.37/0.54             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) !=
% 0.37/0.54               ( k2_tarski @ A @ B ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t74_zfmisc_1])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.37/0.54         != (k2_tarski @ sk_A @ sk_B))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.37/0.54        | (r2_hidden @ sk_A @ sk_C)
% 0.37/0.54        | (r2_hidden @ sk_B @ sk_C))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf('4', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 0.37/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.54  thf(l38_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.54       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.37/0.54         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k2_tarski @ X10 @ X12) @ X13) = (k1_tarski @ X10))
% 0.37/0.55          | ~ (r2_hidden @ X12 @ X13)
% 0.37/0.55          | (r2_hidden @ X10 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ sk_A @ sk_C)
% 0.37/0.55          | (r2_hidden @ X0 @ sk_C)
% 0.37/0.55          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ sk_C) = (k1_tarski @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.37/0.55        | (r2_hidden @ sk_A @ sk_C)
% 0.37/0.55        | (r2_hidden @ sk_A @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('9', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.37/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ (k2_tarski @ X10 @ X12) @ X13) = (k1_tarski @ X10))
% 0.37/0.55          | ~ (r2_hidden @ X12 @ X13)
% 0.37/0.55          | (r2_hidden @ X10 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ X0 @ sk_C)
% 0.37/0.55          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_C) = (k1_tarski @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_tarski @ X0))
% 0.37/0.55          | (r2_hidden @ X0 @ sk_C))),
% 0.37/0.55      inference('sup+', [status(thm)], ['0', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.37/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.55  thf('16', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.37/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.55  thf(t38_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.37/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         ((r1_tarski @ (k2_tarski @ X14 @ X16) @ X17)
% 0.37/0.55          | ~ (r2_hidden @ X16 @ X17)
% 0.37/0.55          | ~ (r2_hidden @ X14 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_C)
% 0.37/0.55          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_A) @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.55  thf('21', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.37/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf(l32_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('25', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

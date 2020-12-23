%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F5z2oli4CC

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:39 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   38 (  60 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  326 ( 792 expanded)
%              Number of equality atoms :   32 (  85 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X9 @ X11 ) @ X12 )
        = ( k2_tarski @ X9 @ X11 ) )
      | ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X12 ) ) ),
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
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X5 @ X7 ) @ X8 )
        = ( k1_tarski @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X8 ) ) ),
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
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X5 @ X7 ) @ X8 )
        = ( k1_tarski @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X8 ) ) ),
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

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X13 @ X15 ) @ X16 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F5z2oli4CC
% 0.15/0.38  % Computer   : n017.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 10:57:31 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 99 iterations in 0.046s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(commutativity_k2_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.54  thf(t72_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.35/0.54       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ (k2_tarski @ X9 @ X11) @ X12)
% 0.35/0.54            = (k2_tarski @ X9 @ X11))
% 0.35/0.54          | (r2_hidden @ X11 @ X12)
% 0.35/0.54          | (r2_hidden @ X9 @ X12))),
% 0.35/0.54      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.35/0.54  thf(t74_zfmisc_1, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ~( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ A ) ) & 
% 0.35/0.54          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ B ) ) & 
% 0.35/0.54          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) !=
% 0.35/0.54            ( k2_tarski @ A @ B ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.54        ( ~( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ A ) ) & 
% 0.35/0.54             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ B ) ) & 
% 0.35/0.54             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) !=
% 0.35/0.54               ( k2_tarski @ A @ B ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t74_zfmisc_1])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.35/0.54         != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.35/0.54        | (r2_hidden @ sk_A @ sk_C)
% 0.35/0.54        | (r2_hidden @ sk_B @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf('4', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 0.35/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.54  thf(l38_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.35/0.54         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ (k2_tarski @ X5 @ X7) @ X8) = (k1_tarski @ X5))
% 0.35/0.54          | ~ (r2_hidden @ X7 @ X8)
% 0.35/0.54          | (r2_hidden @ X5 @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ sk_A @ sk_C)
% 0.35/0.54          | (r2_hidden @ X0 @ sk_C)
% 0.35/0.54          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ sk_C) = (k1_tarski @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.35/0.54        | (r2_hidden @ sk_A @ sk_C)
% 0.35/0.54        | (r2_hidden @ sk_A @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('9', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.35/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ (k2_tarski @ X5 @ X7) @ X8) = (k1_tarski @ X5))
% 0.35/0.54          | ~ (r2_hidden @ X7 @ X8)
% 0.35/0.54          | (r2_hidden @ X5 @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ X0 @ sk_C)
% 0.35/0.54          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_C) = (k1_tarski @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_tarski @ X0))
% 0.35/0.54          | (r2_hidden @ X0 @ sk_C))),
% 0.35/0.54      inference('sup+', [status(thm)], ['0', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.35/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.35/0.54  thf('16', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.35/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.35/0.54  thf(t73_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ (k2_tarski @ X13 @ X15) @ X16) = (k1_xboole_0))
% 0.35/0.54          | ~ (r2_hidden @ X15 @ X16)
% 0.35/0.54          | ~ (r2_hidden @ X13 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_C)
% 0.35/0.54          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_C) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C) = (k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['15', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('23', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AlFPaVRKHG

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  239 ( 330 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X27 )
      | ( r2_hidden @ X25 @ X26 )
      | ( X26
       != ( k2_tarski @ X27 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X24: $i,X27: $i] :
      ( r2_hidden @ X27 @ ( k2_tarski @ X27 @ X24 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('8',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X24: $i,X27: $i] :
      ( r2_hidden @ X27 @ ( k2_tarski @ X27 @ X24 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X26 )
      | ( X28 = X27 )
      | ( X28 = X24 )
      | ( X26
       != ( k2_tarski @ X27 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('15',plain,(
    ! [X24: $i,X27: $i,X28: $i] :
      ( ( X28 = X24 )
      | ( X28 = X27 )
      | ~ ( r2_hidden @ X28 @ ( k2_tarski @ X27 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AlFPaVRKHG
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 190 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(d2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.54         (((X25) != (X27))
% 0.20/0.54          | (r2_hidden @ X25 @ X26)
% 0.20/0.54          | ((X26) != (k2_tarski @ X27 @ X24)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X24 : $i, X27 : $i]: (r2_hidden @ X27 @ (k2_tarski @ X27 @ X24))),
% 0.20/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.54  thf(t1_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.54       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.20/0.54          | (r2_hidden @ X0 @ X3)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r2_hidden @ X1 @ X2)
% 0.20/0.54          | (r2_hidden @ X1 @ (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf(t28_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.54          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.54             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.54         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf(l97_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.54        (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.54         (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X24 : $i, X27 : $i]: (r2_hidden @ X27 @ (k2_tarski @ X27 @ X24))),
% 0.20/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.54  thf(t3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.54          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.54          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (~ (r2_hidden @ sk_A @ 
% 0.20/0.54          (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.54           (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.54  thf('13', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X24 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X28 @ X26)
% 0.20/0.54          | ((X28) = (X27))
% 0.20/0.54          | ((X28) = (X24))
% 0.20/0.54          | ((X26) != (k2_tarski @ X27 @ X24)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X24 : $i, X27 : $i, X28 : $i]:
% 0.20/0.54         (((X28) = (X24))
% 0.20/0.54          | ((X28) = (X27))
% 0.20/0.54          | ~ (r2_hidden @ X28 @ (k2_tarski @ X27 @ X24)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('16', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.54  thf('17', plain, (((sk_A) != (sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('18', plain, (((sk_A) != (sk_C_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('19', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['16', '17', '18'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D5rtBefPVq

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:38 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 ( 456 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X25: $i,X28: $i] :
      ( r2_hidden @ X25 @ ( k2_tarski @ X28 @ X25 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X56 ) @ X57 )
      | ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ X60 @ ( k2_tarski @ X58 @ X61 ) )
      | ( X60
       != ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,(
    ! [X58: $i,X61: $i] :
      ( r1_tarski @ ( k1_tarski @ X58 ) @ ( k2_tarski @ X58 @ X61 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

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

thf('9',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X27 )
      | ( X29 = X28 )
      | ( X29 = X25 )
      | ( X27
       != ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('27',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( X29 = X25 )
      | ( X29 = X28 )
      | ~ ( r2_hidden @ X29 @ ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D5rtBefPVq
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 477 iterations in 0.180s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.63  thf(t69_enumset1, axiom,
% 0.47/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.63  thf('0', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.47/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.63  thf(d2_tarski, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.47/0.63       ( ![D:$i]:
% 0.47/0.63         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.63         (((X26) != (X25))
% 0.47/0.63          | (r2_hidden @ X26 @ X27)
% 0.47/0.63          | ((X27) != (k2_tarski @ X28 @ X25)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      (![X25 : $i, X28 : $i]: (r2_hidden @ X25 @ (k2_tarski @ X28 @ X25))),
% 0.47/0.63      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.63  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['0', '2'])).
% 0.47/0.63  thf(l27_zfmisc_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.47/0.63  thf('4', plain,
% 0.47/0.63      (![X56 : $i, X57 : $i]:
% 0.47/0.63         ((r1_xboole_0 @ (k1_tarski @ X56) @ X57) | (r2_hidden @ X56 @ X57))),
% 0.47/0.63      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.47/0.63  thf(t70_enumset1, axiom,
% 0.47/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.47/0.63  thf('5', plain,
% 0.47/0.63      (![X36 : $i, X37 : $i]:
% 0.47/0.63         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.47/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.63  thf(l45_zfmisc_1, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.47/0.63       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.47/0.63            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.47/0.63  thf('6', plain,
% 0.47/0.63      (![X58 : $i, X60 : $i, X61 : $i]:
% 0.47/0.63         ((r1_tarski @ X60 @ (k2_tarski @ X58 @ X61))
% 0.47/0.63          | ((X60) != (k1_tarski @ X58)))),
% 0.47/0.63      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.47/0.63  thf('7', plain,
% 0.47/0.63      (![X58 : $i, X61 : $i]:
% 0.47/0.63         (r1_tarski @ (k1_tarski @ X58) @ (k2_tarski @ X58 @ X61))),
% 0.47/0.63      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.63  thf('8', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['5', '7'])).
% 0.47/0.63  thf(t28_zfmisc_1, conjecture,
% 0.47/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.47/0.63          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.47/0.63             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.47/0.63  thf('9', plain,
% 0.47/0.63      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t28_xboole_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.63  thf('10', plain,
% 0.47/0.63      (![X17 : $i, X18 : $i]:
% 0.47/0.63         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.47/0.63         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.47/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.63  thf('12', plain,
% 0.47/0.63      (![X36 : $i, X37 : $i]:
% 0.47/0.63         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.47/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.63  thf('13', plain,
% 0.47/0.63      (![X36 : $i, X37 : $i]:
% 0.47/0.63         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.47/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      (((k3_xboole_0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.47/0.63         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))),
% 0.47/0.63      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.47/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.63  thf(t18_xboole_1, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.47/0.63  thf('16', plain,
% 0.47/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.63         ((r1_tarski @ X14 @ X15)
% 0.47/0.63          | ~ (r1_tarski @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.47/0.63      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.47/0.63  thf('17', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.63  thf('18', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r1_tarski @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))
% 0.47/0.63          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['14', '17'])).
% 0.47/0.63  thf('19', plain,
% 0.47/0.63      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.47/0.63      inference('sup-', [status(thm)], ['8', '18'])).
% 0.47/0.63  thf('20', plain,
% 0.47/0.63      (![X17 : $i, X18 : $i]:
% 0.47/0.63         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.47/0.63         = (k1_tarski @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.63  thf(t4_xboole_0, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.63            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.47/0.63          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.47/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.47/0.63          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['4', '23'])).
% 0.47/0.63  thf('25', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.47/0.63      inference('sup-', [status(thm)], ['3', '24'])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X29 @ X27)
% 0.47/0.63          | ((X29) = (X28))
% 0.47/0.63          | ((X29) = (X25))
% 0.47/0.63          | ((X27) != (k2_tarski @ X28 @ X25)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (![X25 : $i, X28 : $i, X29 : $i]:
% 0.47/0.63         (((X29) = (X25))
% 0.47/0.63          | ((X29) = (X28))
% 0.47/0.63          | ~ (r2_hidden @ X29 @ (k2_tarski @ X28 @ X25)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['26'])).
% 0.47/0.63  thf('28', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['25', '27'])).
% 0.47/0.63  thf('29', plain, (((sk_A) != (sk_D_1))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('30', plain, (((sk_A) != (sk_C_1))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('31', plain, ($false),
% 0.47/0.63      inference('simplify_reflect-', [status(thm)], ['28', '29', '30'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.abugXyOvXp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   61 (  70 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  433 ( 536 expanded)
%              Number of equality atoms :   47 (  63 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X70 ) @ ( k2_tarski @ X70 @ X71 ) )
      = ( k1_tarski @ X70 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('15',plain,(
    ! [X66: $i,X68: $i,X69: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X66 @ X68 ) @ X69 )
        = ( k1_tarski @ X66 ) )
      | ( X66 != X68 )
      | ( r2_hidden @ X66 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('16',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X68 @ X68 ) @ X69 )
        = ( k1_tarski @ X68 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X68 ) @ X69 )
        = ( k1_tarski @ X68 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( r2_hidden @ X66 @ X67 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X66 @ X68 ) @ X67 )
       != ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ( r2_hidden @ X29 @ X30 )
      | ( X30
       != ( k2_tarski @ X31 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('27',plain,(
    ! [X28: $i,X31: $i] :
      ( r2_hidden @ X28 @ ( k2_tarski @ X31 @ X28 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X30 )
      | ( X32 = X31 )
      | ( X32 = X28 )
      | ( X30
       != ( k2_tarski @ X31 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('33',plain,(
    ! [X28: $i,X31: $i,X32: $i] :
      ( ( X32 = X28 )
      | ( X32 = X31 )
      | ~ ( r2_hidden @ X32 @ ( k2_tarski @ X31 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.abugXyOvXp
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 823 iterations in 0.350s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(t70_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X39 : $i, X40 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.59/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.79  thf(t19_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.59/0.79       ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X70 : $i, X71 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ (k1_tarski @ X70) @ (k2_tarski @ X70 @ X71))
% 0.59/0.79           = (k1_tarski @ X70))),
% 0.59/0.79      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.59/0.79           = (k1_tarski @ X1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.79  thf(t28_zfmisc_1, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.59/0.79          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.59/0.79             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X39 : $i, X40 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.59/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.59/0.79        (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.79  thf(t17_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.59/0.79      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.79  thf(t1_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.59/0.79       ( r1_tarski @ A @ C ) ))).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X17 @ X18)
% 0.59/0.79          | ~ (r1_tarski @ X18 @ X19)
% 0.59/0.79          | (r1_tarski @ X17 @ X19))),
% 0.59/0.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (r1_tarski @ 
% 0.59/0.79          (k3_xboole_0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1) @ X0) @ 
% 0.59/0.79          (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['6', '9'])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (r1_tarski @ 
% 0.59/0.79          (k3_xboole_0 @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1)) @ 
% 0.59/0.79          (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['3', '10'])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['2', '11'])).
% 0.59/0.79  thf(t28_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X20 : $i, X21 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.59/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.59/0.79         = (k1_tarski @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf(l38_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.79       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.59/0.79         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X66 : $i, X68 : $i, X69 : $i]:
% 0.59/0.79         (((k4_xboole_0 @ (k2_tarski @ X66 @ X68) @ X69) = (k1_tarski @ X66))
% 0.59/0.79          | ((X66) != (X68))
% 0.59/0.79          | (r2_hidden @ X66 @ X69))),
% 0.59/0.79      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X68 : $i, X69 : $i]:
% 0.59/0.79         ((r2_hidden @ X68 @ X69)
% 0.59/0.79          | ((k4_xboole_0 @ (k2_tarski @ X68 @ X68) @ X69) = (k1_tarski @ X68)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.79  thf(t69_enumset1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X68 : $i, X69 : $i]:
% 0.59/0.79         ((r2_hidden @ X68 @ X69)
% 0.59/0.79          | ((k4_xboole_0 @ (k1_tarski @ X68) @ X69) = (k1_tarski @ X68)))),
% 0.59/0.79      inference('demod', [status(thm)], ['16', '17'])).
% 0.59/0.79  thf(t48_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X22 : $i, X23 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.59/0.79           = (k3_xboole_0 @ X22 @ X23))),
% 0.59/0.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X66 @ X67)
% 0.59/0.79          | ((k4_xboole_0 @ (k2_tarski @ X66 @ X68) @ X67) != (k1_tarski @ X66)))),
% 0.59/0.79      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.59/0.79          | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.59/0.79          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['19', '22'])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.59/0.79          | (r2_hidden @ X0 @ X1)
% 0.59/0.79          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['18', '23'])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf(d2_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.59/0.79       ( ![D:$i]:
% 0.59/0.79         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.79         (((X29) != (X28))
% 0.59/0.79          | (r2_hidden @ X29 @ X30)
% 0.59/0.79          | ((X30) != (k2_tarski @ X31 @ X28)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X28 : $i, X31 : $i]: (r2_hidden @ X28 @ (k2_tarski @ X31 @ X28))),
% 0.59/0.79      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.79  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['25', '27'])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((r2_hidden @ X0 @ X1)
% 0.59/0.79          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['24', '28'])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.59/0.79        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '29'])).
% 0.59/0.79  thf('31', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.59/0.79      inference('simplify', [status(thm)], ['30'])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X32 @ X30)
% 0.59/0.79          | ((X32) = (X31))
% 0.59/0.79          | ((X32) = (X28))
% 0.59/0.79          | ((X30) != (k2_tarski @ X31 @ X28)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X28 : $i, X31 : $i, X32 : $i]:
% 0.59/0.79         (((X32) = (X28))
% 0.59/0.79          | ((X32) = (X31))
% 0.59/0.79          | ~ (r2_hidden @ X32 @ (k2_tarski @ X31 @ X28)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['32'])).
% 0.59/0.79  thf('34', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '33'])).
% 0.59/0.79  thf('35', plain, (((sk_A) != (sk_D_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('36', plain, (((sk_A) != (sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('37', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

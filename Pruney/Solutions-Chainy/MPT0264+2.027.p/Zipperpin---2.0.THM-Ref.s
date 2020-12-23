%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FFKJahAcEH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:41 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   71 (  82 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  527 ( 648 expanded)
%              Number of equality atoms :   49 (  63 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X13 ) )
      | ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ X0 ) )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X66 @ X66 @ X67 )
      = ( k2_tarski @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X38 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X31 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X31 @ X32 @ X29 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['30','37'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('39',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X44 @ X43 )
      | ( X44 = X41 )
      | ( X43
       != ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X41: $i,X44: $i] :
      ( ( X44 = X41 )
      | ~ ( r2_hidden @ X44 @ ( k1_tarski @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FFKJahAcEH
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.71/3.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.71/3.94  % Solved by: fo/fo7.sh
% 3.71/3.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.71/3.94  % done 3068 iterations in 3.486s
% 3.71/3.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.71/3.94  % SZS output start Refutation
% 3.71/3.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.71/3.94  thf(sk_B_type, type, sk_B: $i).
% 3.71/3.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.71/3.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.71/3.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.71/3.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.71/3.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.71/3.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.71/3.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.71/3.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.71/3.94  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.71/3.94  thf(sk_A_type, type, sk_A: $i).
% 3.71/3.94  thf(commutativity_k5_xboole_0, axiom,
% 3.71/3.94    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 3.71/3.94  thf('0', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.71/3.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.71/3.94  thf(t59_zfmisc_1, conjecture,
% 3.71/3.94    (![A:$i,B:$i,C:$i]:
% 3.71/3.94     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 3.71/3.94          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 3.71/3.94  thf(zf_stmt_0, negated_conjecture,
% 3.71/3.94    (~( ![A:$i,B:$i,C:$i]:
% 3.71/3.94        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 3.71/3.94             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 3.71/3.94    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 3.71/3.94  thf('1', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 3.71/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.94  thf(t1_xboole_0, axiom,
% 3.71/3.94    (![A:$i,B:$i,C:$i]:
% 3.71/3.94     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 3.71/3.94       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 3.71/3.94  thf('2', plain,
% 3.71/3.94      (![X10 : $i, X11 : $i, X13 : $i]:
% 3.71/3.94         ((r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X13))
% 3.71/3.94          | (r2_hidden @ X10 @ X11)
% 3.71/3.94          | ~ (r2_hidden @ X10 @ X13))),
% 3.71/3.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.71/3.94  thf('3', plain,
% 3.71/3.94      (![X0 : $i]:
% 3.71/3.94         ((r2_hidden @ sk_B @ X0)
% 3.71/3.94          | (r2_hidden @ sk_B @ (k5_xboole_0 @ X0 @ sk_C_1)))),
% 3.71/3.94      inference('sup-', [status(thm)], ['1', '2'])).
% 3.71/3.94  thf('4', plain,
% 3.71/3.94      (![X0 : $i]:
% 3.71/3.94         ((r2_hidden @ sk_B @ (k5_xboole_0 @ sk_C_1 @ X0))
% 3.71/3.94          | (r2_hidden @ sk_B @ X0))),
% 3.71/3.94      inference('sup+', [status(thm)], ['0', '3'])).
% 3.71/3.94  thf('5', plain,
% 3.71/3.94      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 3.71/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.94  thf(t95_xboole_1, axiom,
% 3.71/3.94    (![A:$i,B:$i]:
% 3.71/3.94     ( ( k3_xboole_0 @ A @ B ) =
% 3.71/3.94       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 3.71/3.94  thf('6', plain,
% 3.71/3.94      (![X27 : $i, X28 : $i]:
% 3.71/3.94         ((k3_xboole_0 @ X27 @ X28)
% 3.71/3.94           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 3.71/3.94              (k2_xboole_0 @ X27 @ X28)))),
% 3.71/3.94      inference('cnf', [status(esa)], [t95_xboole_1])).
% 3.71/3.94  thf(t91_xboole_1, axiom,
% 3.71/3.94    (![A:$i,B:$i,C:$i]:
% 3.71/3.94     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.71/3.94       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.71/3.94  thf('7', plain,
% 3.71/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 3.71/3.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 3.71/3.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.71/3.94  thf('8', plain,
% 3.71/3.94      (![X27 : $i, X28 : $i]:
% 3.71/3.94         ((k3_xboole_0 @ X27 @ X28)
% 3.71/3.94           = (k5_xboole_0 @ X27 @ 
% 3.71/3.94              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 3.71/3.94      inference('demod', [status(thm)], ['6', '7'])).
% 3.71/3.94  thf('9', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.71/3.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.71/3.94  thf(t92_xboole_1, axiom,
% 3.71/3.94    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 3.71/3.94  thf('10', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 3.71/3.94      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.71/3.94  thf('11', plain,
% 3.71/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 3.71/3.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 3.71/3.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.71/3.94  thf('12', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]:
% 3.71/3.94         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.71/3.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.71/3.94      inference('sup+', [status(thm)], ['10', '11'])).
% 3.71/3.94  thf('13', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.71/3.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.71/3.94  thf(t5_boole, axiom,
% 3.71/3.94    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.71/3.94  thf('14', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 3.71/3.94      inference('cnf', [status(esa)], [t5_boole])).
% 3.71/3.94  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.71/3.94      inference('sup+', [status(thm)], ['13', '14'])).
% 3.71/3.94  thf('16', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]:
% 3.71/3.94         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.71/3.94      inference('demod', [status(thm)], ['12', '15'])).
% 3.71/3.94  thf('17', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]:
% 3.71/3.94         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.71/3.94      inference('sup+', [status(thm)], ['9', '16'])).
% 3.71/3.94  thf('18', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]:
% 3.71/3.94         ((X1)
% 3.71/3.94           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 3.71/3.94              (k3_xboole_0 @ X1 @ X0)))),
% 3.71/3.94      inference('sup+', [status(thm)], ['8', '17'])).
% 3.71/3.94  thf('19', plain,
% 3.71/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 3.71/3.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 3.71/3.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.71/3.94  thf('20', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.71/3.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.71/3.94  thf('21', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]:
% 3.71/3.94         ((X1)
% 3.71/3.94           = (k5_xboole_0 @ X0 @ 
% 3.71/3.94              (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 3.71/3.94      inference('demod', [status(thm)], ['18', '19', '20'])).
% 3.71/3.94  thf('22', plain,
% 3.71/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 3.71/3.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 3.71/3.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.71/3.94  thf('23', plain,
% 3.71/3.94      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X10 @ X11)
% 3.71/3.94          | ~ (r2_hidden @ X10 @ X12)
% 3.71/3.94          | ~ (r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 3.71/3.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.71/3.94  thf('24', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 3.71/3.94          | ~ (r2_hidden @ X3 @ X0)
% 3.71/3.94          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 3.71/3.94      inference('sup-', [status(thm)], ['22', '23'])).
% 3.71/3.94  thf('25', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X2 @ X0)
% 3.71/3.94          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 3.71/3.94          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.71/3.94      inference('sup-', [status(thm)], ['21', '24'])).
% 3.71/3.94  thf(d3_xboole_0, axiom,
% 3.71/3.94    (![A:$i,B:$i,C:$i]:
% 3.71/3.94     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 3.71/3.94       ( ![D:$i]:
% 3.71/3.94         ( ( r2_hidden @ D @ C ) <=>
% 3.71/3.94           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.71/3.94  thf('26', plain,
% 3.71/3.94      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X2 @ X5)
% 3.71/3.94          | (r2_hidden @ X2 @ X4)
% 3.71/3.94          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 3.71/3.94      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.71/3.94  thf('27', plain,
% 3.71/3.94      (![X2 : $i, X3 : $i, X5 : $i]:
% 3.71/3.94         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 3.71/3.94      inference('simplify', [status(thm)], ['26'])).
% 3.71/3.94  thf('28', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 3.71/3.94          | ~ (r2_hidden @ X2 @ X0))),
% 3.71/3.94      inference('clc', [status(thm)], ['25', '27'])).
% 3.71/3.94  thf('29', plain,
% 3.71/3.94      (![X0 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 3.71/3.94          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 3.71/3.94      inference('sup-', [status(thm)], ['5', '28'])).
% 3.71/3.94  thf('30', plain,
% 3.71/3.94      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 3.71/3.94        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 3.71/3.94      inference('sup-', [status(thm)], ['4', '29'])).
% 3.71/3.94  thf(t70_enumset1, axiom,
% 3.71/3.94    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.71/3.94  thf('31', plain,
% 3.71/3.94      (![X66 : $i, X67 : $i]:
% 3.71/3.94         ((k1_enumset1 @ X66 @ X66 @ X67) = (k2_tarski @ X66 @ X67))),
% 3.71/3.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.71/3.94  thf(d1_enumset1, axiom,
% 3.71/3.94    (![A:$i,B:$i,C:$i,D:$i]:
% 3.71/3.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.71/3.94       ( ![E:$i]:
% 3.71/3.94         ( ( r2_hidden @ E @ D ) <=>
% 3.71/3.94           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 3.71/3.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.71/3.94  thf(zf_stmt_2, axiom,
% 3.71/3.94    (![E:$i,C:$i,B:$i,A:$i]:
% 3.71/3.94     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 3.71/3.94       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 3.71/3.94  thf(zf_stmt_3, axiom,
% 3.71/3.94    (![A:$i,B:$i,C:$i,D:$i]:
% 3.71/3.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.71/3.94       ( ![E:$i]:
% 3.71/3.94         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 3.71/3.94  thf('32', plain,
% 3.71/3.94      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.71/3.94         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 3.71/3.94          | (r2_hidden @ X34 @ X38)
% 3.71/3.94          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 3.71/3.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.71/3.94  thf('33', plain,
% 3.71/3.94      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.71/3.94         ((r2_hidden @ X34 @ (k1_enumset1 @ X37 @ X36 @ X35))
% 3.71/3.94          | (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37))),
% 3.71/3.94      inference('simplify', [status(thm)], ['32'])).
% 3.71/3.94  thf('34', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.94         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 3.71/3.94          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 3.71/3.94      inference('sup+', [status(thm)], ['31', '33'])).
% 3.71/3.94  thf('35', plain,
% 3.71/3.94      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.71/3.94         (((X30) != (X31)) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 3.71/3.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.71/3.94  thf('36', plain,
% 3.71/3.94      (![X29 : $i, X31 : $i, X32 : $i]:
% 3.71/3.94         ~ (zip_tseitin_0 @ X31 @ X31 @ X32 @ X29)),
% 3.71/3.94      inference('simplify', [status(thm)], ['35'])).
% 3.71/3.94  thf('37', plain,
% 3.71/3.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 3.71/3.94      inference('sup-', [status(thm)], ['34', '36'])).
% 3.71/3.94  thf('38', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 3.71/3.94      inference('demod', [status(thm)], ['30', '37'])).
% 3.71/3.94  thf(d1_tarski, axiom,
% 3.71/3.94    (![A:$i,B:$i]:
% 3.71/3.94     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.71/3.94       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.71/3.94  thf('39', plain,
% 3.71/3.94      (![X41 : $i, X43 : $i, X44 : $i]:
% 3.71/3.94         (~ (r2_hidden @ X44 @ X43)
% 3.71/3.94          | ((X44) = (X41))
% 3.71/3.94          | ((X43) != (k1_tarski @ X41)))),
% 3.71/3.94      inference('cnf', [status(esa)], [d1_tarski])).
% 3.71/3.94  thf('40', plain,
% 3.71/3.94      (![X41 : $i, X44 : $i]:
% 3.71/3.94         (((X44) = (X41)) | ~ (r2_hidden @ X44 @ (k1_tarski @ X41)))),
% 3.71/3.94      inference('simplify', [status(thm)], ['39'])).
% 3.71/3.94  thf('41', plain, (((sk_B) = (sk_A))),
% 3.71/3.94      inference('sup-', [status(thm)], ['38', '40'])).
% 3.71/3.94  thf('42', plain, (((sk_A) != (sk_B))),
% 3.71/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.94  thf('43', plain, ($false),
% 3.71/3.94      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 3.71/3.94  
% 3.71/3.94  % SZS output end Refutation
% 3.71/3.94  
% 3.71/3.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

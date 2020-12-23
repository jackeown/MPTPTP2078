%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y7wju2rd5Q

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:49 EST 2020

% Result     : Theorem 41.19s
% Output     : Refutation 41.19s
% Verified   : 
% Statistics : Number of formulae       :   67 (  81 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 ( 608 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( r1_xboole_0 @ X34 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

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

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X36 = X35 )
      | ~ ( r1_xboole_0 @ X36 @ X37 )
      | ( ( k2_xboole_0 @ X37 @ X35 )
       != ( k2_xboole_0 @ X36 @ X38 ) )
      | ~ ( r1_xboole_0 @ X38 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X34: $i] :
      ( r1_xboole_0 @ X34 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k2_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ X51 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k2_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ X51 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

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

thf('36',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y7wju2rd5Q
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:08:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 41.19/41.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 41.19/41.39  % Solved by: fo/fo7.sh
% 41.19/41.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 41.19/41.39  % done 39968 iterations in 40.902s
% 41.19/41.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 41.19/41.39  % SZS output start Refutation
% 41.19/41.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 41.19/41.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 41.19/41.39  thf(sk_B_type, type, sk_B: $i).
% 41.19/41.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 41.19/41.39  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 41.19/41.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 41.19/41.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 41.19/41.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 41.19/41.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 41.19/41.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 41.19/41.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 41.19/41.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 41.19/41.39  thf(sk_A_type, type, sk_A: $i).
% 41.19/41.39  thf(t48_xboole_1, axiom,
% 41.19/41.39    (![A:$i,B:$i]:
% 41.19/41.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 41.19/41.39  thf('0', plain,
% 41.19/41.39      (![X25 : $i, X26 : $i]:
% 41.19/41.39         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 41.19/41.39           = (k3_xboole_0 @ X25 @ X26))),
% 41.19/41.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.19/41.39  thf(fc2_relat_1, axiom,
% 41.19/41.39    (![A:$i,B:$i]:
% 41.19/41.39     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 41.19/41.39  thf('1', plain,
% 41.19/41.39      (![X47 : $i, X48 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X47) | (v1_relat_1 @ (k4_xboole_0 @ X47 @ X48)))),
% 41.19/41.39      inference('cnf', [status(esa)], [fc2_relat_1])).
% 41.19/41.39  thf('2', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 41.19/41.39      inference('sup+', [status(thm)], ['0', '1'])).
% 41.19/41.39  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 41.19/41.39  thf('3', plain, (![X34 : $i]: (r1_xboole_0 @ X34 @ k1_xboole_0)),
% 41.19/41.39      inference('cnf', [status(esa)], [t65_xboole_1])).
% 41.19/41.39  thf(t3_xboole_0, axiom,
% 41.19/41.39    (![A:$i,B:$i]:
% 41.19/41.39     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 41.19/41.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 41.19/41.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 41.19/41.39            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 41.19/41.39  thf('4', plain,
% 41.19/41.39      (![X4 : $i, X5 : $i]:
% 41.19/41.39         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 41.19/41.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 41.19/41.39  thf(t4_xboole_0, axiom,
% 41.19/41.39    (![A:$i,B:$i]:
% 41.19/41.39     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 41.19/41.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 41.19/41.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 41.19/41.39            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 41.19/41.39  thf('5', plain,
% 41.19/41.39      (![X8 : $i, X10 : $i, X11 : $i]:
% 41.19/41.39         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 41.19/41.39          | ~ (r1_xboole_0 @ X8 @ X11))),
% 41.19/41.39      inference('cnf', [status(esa)], [t4_xboole_0])).
% 41.19/41.39  thf('6', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.19/41.39         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 41.19/41.39          | ~ (r1_xboole_0 @ X1 @ X0))),
% 41.19/41.39      inference('sup-', [status(thm)], ['4', '5'])).
% 41.19/41.39  thf('7', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 41.19/41.39      inference('sup-', [status(thm)], ['3', '6'])).
% 41.19/41.39  thf(t1_boole, axiom,
% 41.19/41.39    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 41.19/41.39  thf('8', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 41.19/41.39      inference('cnf', [status(esa)], [t1_boole])).
% 41.19/41.39  thf('9', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 41.19/41.39      inference('cnf', [status(esa)], [t1_boole])).
% 41.19/41.39  thf(t72_xboole_1, axiom,
% 41.19/41.39    (![A:$i,B:$i,C:$i,D:$i]:
% 41.19/41.39     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 41.19/41.39         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 41.19/41.39       ( ( C ) = ( B ) ) ))).
% 41.19/41.39  thf('10', plain,
% 41.19/41.39      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 41.19/41.39         (((X36) = (X35))
% 41.19/41.39          | ~ (r1_xboole_0 @ X36 @ X37)
% 41.19/41.39          | ((k2_xboole_0 @ X37 @ X35) != (k2_xboole_0 @ X36 @ X38))
% 41.19/41.39          | ~ (r1_xboole_0 @ X38 @ X35))),
% 41.19/41.39      inference('cnf', [status(esa)], [t72_xboole_1])).
% 41.19/41.39  thf('11', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.19/41.39         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 41.19/41.39          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 41.19/41.39          | ~ (r1_xboole_0 @ X2 @ X0)
% 41.19/41.39          | ((X2) = (k1_xboole_0)))),
% 41.19/41.39      inference('sup-', [status(thm)], ['9', '10'])).
% 41.19/41.39  thf('12', plain, (![X34 : $i]: (r1_xboole_0 @ X34 @ k1_xboole_0)),
% 41.19/41.39      inference('cnf', [status(esa)], [t65_xboole_1])).
% 41.19/41.39  thf('13', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.19/41.39         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 41.19/41.39          | ~ (r1_xboole_0 @ X2 @ X0)
% 41.19/41.39          | ((X2) = (k1_xboole_0)))),
% 41.19/41.39      inference('demod', [status(thm)], ['11', '12'])).
% 41.19/41.39  thf('14', plain,
% 41.19/41.39      (![X1 : $i, X2 : $i]:
% 41.19/41.39         (((X2) = (k1_xboole_0))
% 41.19/41.39          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X1)))),
% 41.19/41.39      inference('simplify', [status(thm)], ['13'])).
% 41.19/41.39  thf('15', plain,
% 41.19/41.39      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 41.19/41.39      inference('sup-', [status(thm)], ['8', '14'])).
% 41.19/41.39  thf('16', plain,
% 41.19/41.39      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 41.19/41.39      inference('sup-', [status(thm)], ['7', '15'])).
% 41.19/41.39  thf(t31_xboole_1, axiom,
% 41.19/41.39    (![A:$i,B:$i,C:$i]:
% 41.19/41.39     ( r1_tarski @
% 41.19/41.39       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 41.19/41.39       ( k2_xboole_0 @ B @ C ) ))).
% 41.19/41.39  thf('17', plain,
% 41.19/41.39      (![X17 : $i, X18 : $i, X19 : $i]:
% 41.19/41.39         (r1_tarski @ 
% 41.19/41.39          (k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k3_xboole_0 @ X17 @ X19)) @ 
% 41.19/41.39          (k2_xboole_0 @ X18 @ X19))),
% 41.19/41.39      inference('cnf', [status(esa)], [t31_xboole_1])).
% 41.19/41.39  thf('18', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 41.19/41.39          (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 41.19/41.39      inference('sup+', [status(thm)], ['16', '17'])).
% 41.19/41.39  thf('19', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 41.19/41.39      inference('cnf', [status(esa)], [t1_boole])).
% 41.19/41.39  thf('20', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 41.19/41.39      inference('cnf', [status(esa)], [t1_boole])).
% 41.19/41.39  thf('21', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 41.19/41.39      inference('demod', [status(thm)], ['18', '19', '20'])).
% 41.19/41.39  thf(t25_relat_1, axiom,
% 41.19/41.39    (![A:$i]:
% 41.19/41.39     ( ( v1_relat_1 @ A ) =>
% 41.19/41.39       ( ![B:$i]:
% 41.19/41.39         ( ( v1_relat_1 @ B ) =>
% 41.19/41.39           ( ( r1_tarski @ A @ B ) =>
% 41.19/41.39             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 41.19/41.39               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 41.19/41.39  thf('22', plain,
% 41.19/41.39      (![X50 : $i, X51 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X50)
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ X51) @ (k2_relat_1 @ X50))
% 41.19/41.39          | ~ (r1_tarski @ X51 @ X50)
% 41.19/41.39          | ~ (v1_relat_1 @ X51))),
% 41.19/41.39      inference('cnf', [status(esa)], [t25_relat_1])).
% 41.19/41.39  thf('23', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 41.19/41.39             (k2_relat_1 @ X0))
% 41.19/41.39          | ~ (v1_relat_1 @ X0))),
% 41.19/41.39      inference('sup-', [status(thm)], ['21', '22'])).
% 41.19/41.39  thf('24', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X1)
% 41.19/41.39          | ~ (v1_relat_1 @ X0)
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 41.19/41.39             (k2_relat_1 @ X0)))),
% 41.19/41.39      inference('sup-', [status(thm)], ['2', '23'])).
% 41.19/41.39  thf('25', plain,
% 41.19/41.39      (![X25 : $i, X26 : $i]:
% 41.19/41.39         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 41.19/41.39           = (k3_xboole_0 @ X25 @ X26))),
% 41.19/41.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.19/41.39  thf(t36_xboole_1, axiom,
% 41.19/41.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 41.19/41.39  thf('26', plain,
% 41.19/41.39      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 41.19/41.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 41.19/41.39  thf('27', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 41.19/41.39      inference('sup+', [status(thm)], ['25', '26'])).
% 41.19/41.39  thf('28', plain,
% 41.19/41.39      (![X50 : $i, X51 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X50)
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ X51) @ (k2_relat_1 @ X50))
% 41.19/41.39          | ~ (r1_tarski @ X51 @ X50)
% 41.19/41.39          | ~ (v1_relat_1 @ X51))),
% 41.19/41.39      inference('cnf', [status(esa)], [t25_relat_1])).
% 41.19/41.39  thf('29', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 41.19/41.39             (k2_relat_1 @ X0))
% 41.19/41.39          | ~ (v1_relat_1 @ X0))),
% 41.19/41.39      inference('sup-', [status(thm)], ['27', '28'])).
% 41.19/41.39  thf('30', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 41.19/41.39      inference('sup+', [status(thm)], ['0', '1'])).
% 41.19/41.39  thf('31', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X0)
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 41.19/41.39             (k2_relat_1 @ X0)))),
% 41.19/41.39      inference('clc', [status(thm)], ['29', '30'])).
% 41.19/41.39  thf(t19_xboole_1, axiom,
% 41.19/41.39    (![A:$i,B:$i,C:$i]:
% 41.19/41.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 41.19/41.39       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 41.19/41.39  thf('32', plain,
% 41.19/41.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 41.19/41.39         (~ (r1_tarski @ X12 @ X13)
% 41.19/41.39          | ~ (r1_tarski @ X12 @ X14)
% 41.19/41.39          | (r1_tarski @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 41.19/41.39      inference('cnf', [status(esa)], [t19_xboole_1])).
% 41.19/41.39  thf('33', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X0)
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 41.19/41.39             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 41.19/41.39          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 41.19/41.39      inference('sup-', [status(thm)], ['31', '32'])).
% 41.19/41.39  thf('34', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         (~ (v1_relat_1 @ X0)
% 41.19/41.39          | ~ (v1_relat_1 @ X1)
% 41.19/41.39          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 41.19/41.39             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 41.19/41.39          | ~ (v1_relat_1 @ X1))),
% 41.19/41.39      inference('sup-', [status(thm)], ['24', '33'])).
% 41.19/41.39  thf('35', plain,
% 41.19/41.39      (![X0 : $i, X1 : $i]:
% 41.19/41.39         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 41.19/41.39           (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 41.19/41.39          | ~ (v1_relat_1 @ X1)
% 41.19/41.39          | ~ (v1_relat_1 @ X0))),
% 41.19/41.39      inference('simplify', [status(thm)], ['34'])).
% 41.19/41.39  thf(t27_relat_1, conjecture,
% 41.19/41.39    (![A:$i]:
% 41.19/41.39     ( ( v1_relat_1 @ A ) =>
% 41.19/41.39       ( ![B:$i]:
% 41.19/41.39         ( ( v1_relat_1 @ B ) =>
% 41.19/41.39           ( r1_tarski @
% 41.19/41.39             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 41.19/41.39             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 41.19/41.39  thf(zf_stmt_0, negated_conjecture,
% 41.19/41.39    (~( ![A:$i]:
% 41.19/41.39        ( ( v1_relat_1 @ A ) =>
% 41.19/41.39          ( ![B:$i]:
% 41.19/41.39            ( ( v1_relat_1 @ B ) =>
% 41.19/41.39              ( r1_tarski @
% 41.19/41.39                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 41.19/41.39                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 41.19/41.39    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 41.19/41.39  thf('36', plain,
% 41.19/41.39      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 41.19/41.39          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 41.19/41.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.19/41.39  thf('37', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_A))),
% 41.19/41.39      inference('sup-', [status(thm)], ['35', '36'])).
% 41.19/41.39  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 41.19/41.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.19/41.39  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 41.19/41.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.19/41.39  thf('40', plain, ($false),
% 41.19/41.39      inference('demod', [status(thm)], ['37', '38', '39'])).
% 41.19/41.39  
% 41.19/41.39  % SZS output end Refutation
% 41.19/41.39  
% 41.23/41.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

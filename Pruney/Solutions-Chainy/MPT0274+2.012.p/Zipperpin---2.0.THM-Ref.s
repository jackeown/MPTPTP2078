%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LzqLBkGBDX

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:33 EST 2020

% Result     : Theorem 12.63s
% Output     : Refutation 12.63s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 221 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  677 (2325 expanded)
%              Number of equality atoms :   48 ( 156 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

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

thf('18',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X26 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('28',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','21','31','32','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( r2_hidden @ X65 @ X66 )
      | ( r1_xboole_0 @ ( k2_tarski @ X65 @ X67 ) @ X66 )
      | ( r2_hidden @ X67 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('47',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','21','31','32'])).

thf('48',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','21'])).

thf('53',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(clc,[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['35','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LzqLBkGBDX
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 12.63/12.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.63/12.84  % Solved by: fo/fo7.sh
% 12.63/12.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.63/12.84  % done 3382 iterations in 12.396s
% 12.63/12.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.63/12.84  % SZS output start Refutation
% 12.63/12.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.63/12.84  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 12.63/12.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.63/12.84  thf(sk_B_type, type, sk_B: $i).
% 12.63/12.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.63/12.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 12.63/12.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 12.63/12.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.63/12.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.63/12.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.63/12.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 12.63/12.84  thf(sk_A_type, type, sk_A: $i).
% 12.63/12.84  thf(t72_zfmisc_1, conjecture,
% 12.63/12.84    (![A:$i,B:$i,C:$i]:
% 12.63/12.84     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 12.63/12.84       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 12.63/12.84  thf(zf_stmt_0, negated_conjecture,
% 12.63/12.84    (~( ![A:$i,B:$i,C:$i]:
% 12.63/12.84        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 12.63/12.84          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 12.63/12.84    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 12.63/12.84  thf('0', plain,
% 12.63/12.84      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 12.63/12.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84            = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.63/12.84  thf('1', plain,
% 12.63/12.84      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 12.63/12.84      inference('split', [status(esa)], ['0'])).
% 12.63/12.84  thf('2', plain,
% 12.63/12.84      ((~ (r2_hidden @ sk_A @ sk_C_1)
% 12.63/12.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84            = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.63/12.84  thf('3', plain,
% 12.63/12.84      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 12.63/12.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('split', [status(esa)], ['2'])).
% 12.63/12.84  thf(t70_enumset1, axiom,
% 12.63/12.84    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 12.63/12.84  thf('4', plain,
% 12.63/12.84      (![X36 : $i, X37 : $i]:
% 12.63/12.84         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 12.63/12.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.63/12.84  thf(d1_enumset1, axiom,
% 12.63/12.84    (![A:$i,B:$i,C:$i,D:$i]:
% 12.63/12.84     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 12.63/12.84       ( ![E:$i]:
% 12.63/12.84         ( ( r2_hidden @ E @ D ) <=>
% 12.63/12.84           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 12.63/12.84  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 12.63/12.84  thf(zf_stmt_2, axiom,
% 12.63/12.84    (![E:$i,C:$i,B:$i,A:$i]:
% 12.63/12.84     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 12.63/12.84       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 12.63/12.84  thf(zf_stmt_3, axiom,
% 12.63/12.84    (![A:$i,B:$i,C:$i,D:$i]:
% 12.63/12.84     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 12.63/12.84       ( ![E:$i]:
% 12.63/12.84         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 12.63/12.84  thf('5', plain,
% 12.63/12.84      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 12.63/12.84         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 12.63/12.84          | (r2_hidden @ X29 @ X33)
% 12.63/12.84          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 12.63/12.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.63/12.84  thf('6', plain,
% 12.63/12.84      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 12.63/12.84         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 12.63/12.84          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 12.63/12.84      inference('simplify', [status(thm)], ['5'])).
% 12.63/12.84  thf('7', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.63/12.84         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 12.63/12.84          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 12.63/12.84      inference('sup+', [status(thm)], ['4', '6'])).
% 12.63/12.84  thf('8', plain,
% 12.63/12.84      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 12.63/12.84         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 12.63/12.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.63/12.84  thf('9', plain,
% 12.63/12.84      (![X24 : $i, X26 : $i, X27 : $i]:
% 12.63/12.84         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 12.63/12.84      inference('simplify', [status(thm)], ['8'])).
% 12.63/12.84  thf('10', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 12.63/12.84      inference('sup-', [status(thm)], ['7', '9'])).
% 12.63/12.84  thf('11', plain,
% 12.63/12.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B)))
% 12.63/12.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))))),
% 12.63/12.84      inference('split', [status(esa)], ['2'])).
% 12.63/12.84  thf(t79_xboole_1, axiom,
% 12.63/12.84    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 12.63/12.84  thf('12', plain,
% 12.63/12.84      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 12.63/12.84      inference('cnf', [status(esa)], [t79_xboole_1])).
% 12.63/12.84  thf('13', plain,
% 12.63/12.84      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 12.63/12.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))))),
% 12.63/12.84      inference('sup+', [status(thm)], ['11', '12'])).
% 12.63/12.84  thf(symmetry_r1_xboole_0, axiom,
% 12.63/12.84    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 12.63/12.84  thf('14', plain,
% 12.63/12.84      (![X5 : $i, X6 : $i]:
% 12.63/12.84         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 12.63/12.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 12.63/12.84  thf('15', plain,
% 12.63/12.84      (((r1_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 12.63/12.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))))),
% 12.63/12.84      inference('sup-', [status(thm)], ['13', '14'])).
% 12.63/12.84  thf('16', plain,
% 12.63/12.84      (((r2_hidden @ sk_B @ sk_C_1)
% 12.63/12.84        | (r2_hidden @ sk_A @ sk_C_1)
% 12.63/12.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84            != (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.63/12.84  thf('17', plain,
% 12.63/12.84      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 12.63/12.84      inference('split', [status(esa)], ['16'])).
% 12.63/12.84  thf(t3_xboole_0, axiom,
% 12.63/12.84    (![A:$i,B:$i]:
% 12.63/12.84     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 12.63/12.84            ( r1_xboole_0 @ A @ B ) ) ) & 
% 12.63/12.84       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 12.63/12.84            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 12.63/12.84  thf('18', plain,
% 12.63/12.84      (![X7 : $i, X9 : $i, X10 : $i]:
% 12.63/12.84         (~ (r2_hidden @ X9 @ X7)
% 12.63/12.84          | ~ (r2_hidden @ X9 @ X10)
% 12.63/12.84          | ~ (r1_xboole_0 @ X7 @ X10))),
% 12.63/12.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 12.63/12.84  thf('19', plain,
% 12.63/12.84      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 12.63/12.84         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['17', '18'])).
% 12.63/12.84  thf('20', plain,
% 12.63/12.84      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B)))
% 12.63/12.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))) & 
% 12.63/12.84             ((r2_hidden @ sk_A @ sk_C_1)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['15', '19'])).
% 12.63/12.84  thf('21', plain,
% 12.63/12.84      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 12.63/12.84       ~
% 12.63/12.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['10', '20'])).
% 12.63/12.84  thf('22', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.63/12.84         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 12.63/12.84          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 12.63/12.84      inference('sup+', [status(thm)], ['4', '6'])).
% 12.63/12.84  thf('23', plain,
% 12.63/12.84      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 12.63/12.84         (((X25) != (X26)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 12.63/12.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.63/12.84  thf('24', plain,
% 12.63/12.84      (![X24 : $i, X26 : $i, X27 : $i]:
% 12.63/12.84         ~ (zip_tseitin_0 @ X26 @ X26 @ X27 @ X24)),
% 12.63/12.84      inference('simplify', [status(thm)], ['23'])).
% 12.63/12.84  thf('25', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 12.63/12.84      inference('sup-', [status(thm)], ['22', '24'])).
% 12.63/12.84  thf('26', plain,
% 12.63/12.84      (((r1_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 12.63/12.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))))),
% 12.63/12.84      inference('sup-', [status(thm)], ['13', '14'])).
% 12.63/12.84  thf('27', plain,
% 12.63/12.84      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 12.63/12.84      inference('split', [status(esa)], ['16'])).
% 12.63/12.84  thf('28', plain,
% 12.63/12.84      (![X7 : $i, X9 : $i, X10 : $i]:
% 12.63/12.84         (~ (r2_hidden @ X9 @ X7)
% 12.63/12.84          | ~ (r2_hidden @ X9 @ X10)
% 12.63/12.84          | ~ (r1_xboole_0 @ X7 @ X10))),
% 12.63/12.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 12.63/12.84  thf('29', plain,
% 12.63/12.84      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_B @ X0)))
% 12.63/12.84         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['27', '28'])).
% 12.63/12.84  thf('30', plain,
% 12.63/12.84      ((~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))
% 12.63/12.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))) & 
% 12.63/12.84             ((r2_hidden @ sk_B @ sk_C_1)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['26', '29'])).
% 12.63/12.84  thf('31', plain,
% 12.63/12.84      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 12.63/12.84       ~
% 12.63/12.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['25', '30'])).
% 12.63/12.84  thf('32', plain,
% 12.63/12.84      (~
% 12.63/12.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B))) | 
% 12.63/12.84       ((r2_hidden @ sk_B @ sk_C_1)) | ((r2_hidden @ sk_A @ sk_C_1))),
% 12.63/12.84      inference('split', [status(esa)], ['16'])).
% 12.63/12.84  thf('33', plain,
% 12.63/12.84      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 12.63/12.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('split', [status(esa)], ['0'])).
% 12.63/12.84  thf('34', plain, (~ ((r2_hidden @ sk_B @ sk_C_1))),
% 12.63/12.84      inference('sat_resolution*', [status(thm)], ['3', '21', '31', '32', '33'])).
% 12.63/12.84  thf('35', plain, (~ (r2_hidden @ sk_B @ sk_C_1)),
% 12.63/12.84      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 12.63/12.84  thf(t57_zfmisc_1, axiom,
% 12.63/12.84    (![A:$i,B:$i,C:$i]:
% 12.63/12.84     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 12.63/12.84          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 12.63/12.84  thf('36', plain,
% 12.63/12.84      (![X65 : $i, X66 : $i, X67 : $i]:
% 12.63/12.84         ((r2_hidden @ X65 @ X66)
% 12.63/12.84          | (r1_xboole_0 @ (k2_tarski @ X65 @ X67) @ X66)
% 12.63/12.84          | (r2_hidden @ X67 @ X66))),
% 12.63/12.84      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 12.63/12.84  thf(d7_xboole_0, axiom,
% 12.63/12.84    (![A:$i,B:$i]:
% 12.63/12.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 12.63/12.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 12.63/12.84  thf('37', plain,
% 12.63/12.84      (![X2 : $i, X3 : $i]:
% 12.63/12.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 12.63/12.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.63/12.84  thf('38', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.63/12.84         ((r2_hidden @ X1 @ X0)
% 12.63/12.84          | (r2_hidden @ X2 @ X0)
% 12.63/12.84          | ((k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 12.63/12.84      inference('sup-', [status(thm)], ['36', '37'])).
% 12.63/12.84  thf(t100_xboole_1, axiom,
% 12.63/12.84    (![A:$i,B:$i]:
% 12.63/12.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.63/12.84  thf('39', plain,
% 12.63/12.84      (![X11 : $i, X12 : $i]:
% 12.63/12.84         ((k4_xboole_0 @ X11 @ X12)
% 12.63/12.84           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.63/12.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.63/12.84  thf('40', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.63/12.84         (((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)
% 12.63/12.84            = (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ k1_xboole_0))
% 12.63/12.84          | (r2_hidden @ X2 @ X0)
% 12.63/12.84          | (r2_hidden @ X1 @ X0))),
% 12.63/12.84      inference('sup+', [status(thm)], ['38', '39'])).
% 12.63/12.84  thf(commutativity_k5_xboole_0, axiom,
% 12.63/12.84    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 12.63/12.84  thf('41', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 12.63/12.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 12.63/12.84  thf('42', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 12.63/12.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 12.63/12.84  thf(t5_boole, axiom,
% 12.63/12.84    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.63/12.84  thf('43', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 12.63/12.84      inference('cnf', [status(esa)], [t5_boole])).
% 12.63/12.84  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.63/12.84      inference('sup+', [status(thm)], ['42', '43'])).
% 12.63/12.84  thf('45', plain,
% 12.63/12.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.63/12.84         (((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1))
% 12.63/12.84          | (r2_hidden @ X2 @ X0)
% 12.63/12.84          | (r2_hidden @ X1 @ X0))),
% 12.63/12.84      inference('demod', [status(thm)], ['40', '41', '44'])).
% 12.63/12.84  thf('46', plain,
% 12.63/12.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          != (k2_tarski @ sk_A @ sk_B)))
% 12.63/12.84         <= (~
% 12.63/12.84             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84                = (k2_tarski @ sk_A @ sk_B))))),
% 12.63/12.84      inference('split', [status(esa)], ['16'])).
% 12.63/12.84  thf('47', plain,
% 12.63/12.84      (~
% 12.63/12.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84          = (k2_tarski @ sk_A @ sk_B)))),
% 12.63/12.84      inference('sat_resolution*', [status(thm)], ['3', '21', '31', '32'])).
% 12.63/12.84  thf('48', plain,
% 12.63/12.84      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 12.63/12.84         != (k2_tarski @ sk_A @ sk_B))),
% 12.63/12.84      inference('simpl_trail', [status(thm)], ['46', '47'])).
% 12.63/12.84  thf('49', plain,
% 12.63/12.84      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 12.63/12.84        | (r2_hidden @ sk_B @ sk_C_1)
% 12.63/12.84        | (r2_hidden @ sk_A @ sk_C_1))),
% 12.63/12.84      inference('sup-', [status(thm)], ['45', '48'])).
% 12.63/12.84  thf('50', plain,
% 12.63/12.84      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B @ sk_C_1))),
% 12.63/12.84      inference('simplify', [status(thm)], ['49'])).
% 12.63/12.84  thf('51', plain,
% 12.63/12.84      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 12.63/12.84      inference('split', [status(esa)], ['2'])).
% 12.63/12.84  thf('52', plain, (~ ((r2_hidden @ sk_A @ sk_C_1))),
% 12.63/12.84      inference('sat_resolution*', [status(thm)], ['3', '21'])).
% 12.63/12.84  thf('53', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 12.63/12.84      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 12.63/12.84  thf('54', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 12.63/12.84      inference('clc', [status(thm)], ['50', '53'])).
% 12.63/12.84  thf('55', plain, ($false), inference('demod', [status(thm)], ['35', '54'])).
% 12.63/12.84  
% 12.63/12.84  % SZS output end Refutation
% 12.63/12.84  
% 12.63/12.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

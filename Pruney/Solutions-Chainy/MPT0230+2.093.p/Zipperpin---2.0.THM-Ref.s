%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vb2xBLNg5G

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:21 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   82 (  95 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  648 ( 786 expanded)
%              Number of equality atoms :   68 (  87 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ X11 @ ( sk_D @ X11 @ X10 @ X9 ) )
      | ( X10
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_B @ sk_C_1 )
        = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( sk_D @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ sk_C_1 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( r1_tarski @ X10 @ ( sk_D @ X11 @ X10 @ X9 ) )
      | ( X10
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_B @ sk_C_1 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
    | ( ( k2_tarski @ sk_B @ sk_C_1 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_tarski @ sk_B @ sk_C_1 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
    | ( ( k2_tarski @ sk_B @ sk_C_1 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( k2_tarski @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t136_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
         != ( k2_tarski @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 = X30 )
      | ( ( k4_xboole_0 @ ( k1_enumset1 @ X31 @ X30 @ X32 ) @ ( k1_tarski @ X31 ) )
        = ( k2_tarski @ X30 @ X32 ) )
      | ( X31 = X32 ) ) ),
    inference(cnf,[status(esa)],[t136_enumset1])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) @ X20 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( X2 = X0 )
      | ( X2 = X1 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf(t96_enumset1,axiom,(
    ! [A: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X39: $i] :
      ( ( k6_enumset1 @ X39 @ X39 @ X39 @ X39 @ X39 @ X39 @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t96_enumset1])).

thf(t93_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k6_enumset1 @ X36 @ X36 @ X36 @ X36 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t93_enumset1])).

thf('29',plain,(
    ! [X39: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k2_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('39',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X40 @ X42 ) @ X41 )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('47',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vb2xBLNg5G
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:35:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 810 iterations in 0.402s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.67/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.67/0.86                                           $i > $i).
% 0.67/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.67/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.67/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(d10_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.86  thf('0', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('1', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.67/0.86      inference('simplify', [status(thm)], ['0'])).
% 0.67/0.86  thf(t25_zfmisc_1, conjecture,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.67/0.86          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.86        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.67/0.86             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t14_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.67/0.86         ( ![D:$i]:
% 0.67/0.86           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.67/0.86             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.67/0.86       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.67/0.86  thf('3', plain,
% 0.67/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (r1_tarski @ X9 @ X10)
% 0.67/0.86          | ~ (r1_tarski @ X11 @ X10)
% 0.67/0.86          | (r1_tarski @ X11 @ (sk_D @ X11 @ X10 @ X9))
% 0.67/0.86          | ((X10) = (k2_xboole_0 @ X9 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.67/0.86  thf('4', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86            = (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.67/0.86          | (r1_tarski @ X0 @ 
% 0.67/0.86             (sk_D @ X0 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_tarski @ sk_A)))
% 0.67/0.86          | ~ (r1_tarski @ X0 @ (k2_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      (((r1_tarski @ (k2_tarski @ sk_B @ sk_C_1) @ 
% 0.67/0.86         (sk_D @ (k2_tarski @ sk_B @ sk_C_1) @ (k2_tarski @ sk_B @ sk_C_1) @ 
% 0.67/0.86          (k1_tarski @ sk_A)))
% 0.67/0.86        | ((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86            = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['1', '4'])).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (r1_tarski @ X9 @ X10)
% 0.67/0.86          | ~ (r1_tarski @ X11 @ X10)
% 0.67/0.86          | ~ (r1_tarski @ X10 @ (sk_D @ X11 @ X10 @ X9))
% 0.67/0.86          | ((X10) = (k2_xboole_0 @ X9 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.67/0.86  thf('7', plain,
% 0.67/0.86      ((((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86          = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1)))
% 0.67/0.86        | ((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86            = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1)))
% 0.67/0.86        | ~ (r1_tarski @ (k2_tarski @ sk_B @ sk_C_1) @ 
% 0.67/0.86             (k2_tarski @ sk_B @ sk_C_1))
% 0.67/0.86        | ~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.86  thf('8', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.67/0.86      inference('simplify', [status(thm)], ['0'])).
% 0.67/0.86  thf('9', plain,
% 0.67/0.86      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('10', plain,
% 0.67/0.86      ((((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86          = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1)))
% 0.67/0.86        | ((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86            = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))))),
% 0.67/0.86      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.67/0.86  thf('11', plain,
% 0.67/0.86      (((k2_tarski @ sk_B @ sk_C_1)
% 0.67/0.86         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['10'])).
% 0.67/0.86  thf(t21_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.67/0.86  thf('12', plain,
% 0.67/0.86      (![X12 : $i, X13 : $i]:
% 0.67/0.86         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.67/0.86  thf('13', plain,
% 0.67/0.86      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))
% 0.67/0.86         = (k1_tarski @ sk_A))),
% 0.67/0.86      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.86  thf(t136_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 0.67/0.86          ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 0.67/0.86            ( k2_tarski @ B @ C ) ) ) ))).
% 0.67/0.86  thf('14', plain,
% 0.67/0.86      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.86         (((X31) = (X30))
% 0.67/0.86          | ((k4_xboole_0 @ (k1_enumset1 @ X31 @ X30 @ X32) @ (k1_tarski @ X31))
% 0.67/0.86              = (k2_tarski @ X30 @ X32))
% 0.67/0.86          | ((X31) = (X32)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t136_enumset1])).
% 0.67/0.86  thf(t90_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.67/0.86  thf('15', plain,
% 0.67/0.86      (![X19 : $i, X20 : $i]:
% 0.67/0.86         (r1_xboole_0 @ (k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)) @ X20)),
% 0.67/0.86      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.67/0.86  thf(t47_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.67/0.86  thf('16', plain,
% 0.67/0.86      (![X17 : $i, X18 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.67/0.86           = (k4_xboole_0 @ X17 @ X18))),
% 0.67/0.86      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.67/0.86  thf('17', plain,
% 0.67/0.86      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 0.67/0.86      inference('demod', [status(thm)], ['15', '16'])).
% 0.67/0.86  thf(symmetry_r1_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.67/0.86  thf('18', plain,
% 0.67/0.86      (![X4 : $i, X5 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.67/0.86      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['17', '18'])).
% 0.67/0.86  thf(d7_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.67/0.86       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.86  thf('21', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.86  thf('22', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.86         (((k3_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.67/0.86            = (k1_xboole_0))
% 0.67/0.86          | ((X2) = (X0))
% 0.67/0.86          | ((X2) = (X1)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['14', '21'])).
% 0.67/0.86  thf('23', plain,
% 0.67/0.86      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.67/0.86        | ((sk_A) = (sk_B))
% 0.67/0.86        | ((sk_A) = (sk_C_1)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['13', '22'])).
% 0.67/0.86  thf('24', plain, (((sk_A) != (sk_C_1))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('25', plain, (((sk_A) != (sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('26', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.67/0.86      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.67/0.86  thf(t96_enumset1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.67/0.86  thf('27', plain,
% 0.67/0.86      (![X39 : $i]:
% 0.67/0.86         ((k6_enumset1 @ X39 @ X39 @ X39 @ X39 @ X39 @ X39 @ X39 @ X39)
% 0.67/0.86           = (k1_tarski @ X39))),
% 0.67/0.86      inference('cnf', [status(esa)], [t96_enumset1])).
% 0.67/0.86  thf(t93_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C ) =
% 0.67/0.86       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.67/0.86  thf('28', plain,
% 0.67/0.86      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.67/0.86         ((k6_enumset1 @ X36 @ X36 @ X36 @ X36 @ X36 @ X36 @ X37 @ X38)
% 0.67/0.86           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.67/0.86      inference('cnf', [status(esa)], [t93_enumset1])).
% 0.67/0.86  thf('29', plain,
% 0.67/0.86      (![X39 : $i]: ((k1_enumset1 @ X39 @ X39 @ X39) = (k1_tarski @ X39))),
% 0.67/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.67/0.86  thf(t71_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.67/0.86  thf('30', plain,
% 0.67/0.86      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.67/0.86         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 0.67/0.86           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.67/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.67/0.86  thf(l53_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.67/0.86       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.86         ((k2_enumset1 @ X26 @ X27 @ X28 @ X29)
% 0.67/0.86           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k2_tarski @ X28 @ X29)))),
% 0.67/0.86      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.67/0.86  thf('32', plain,
% 0.67/0.86      (![X12 : $i, X13 : $i]:
% 0.67/0.86         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.67/0.86  thf('33', plain,
% 0.67/0.86      (![X17 : $i, X18 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.67/0.86           = (k4_xboole_0 @ X17 @ X18))),
% 0.67/0.86      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.67/0.86  thf('34', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ X0 @ X0)
% 0.67/0.86           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('35', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.67/0.86      inference('simplify', [status(thm)], ['0'])).
% 0.67/0.86  thf(t37_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.86  thf('36', plain,
% 0.67/0.86      (![X14 : $i, X16 : $i]:
% 0.67/0.86         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 0.67/0.86          | ~ (r1_tarski @ X14 @ X16))),
% 0.67/0.86      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.67/0.86  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.86  thf('38', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['34', '37'])).
% 0.67/0.86  thf(l38_zfmisc_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.67/0.86       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.67/0.86         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.67/0.86  thf('39', plain,
% 0.67/0.86      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X40 @ X41)
% 0.67/0.86          | ((k4_xboole_0 @ (k2_tarski @ X40 @ X42) @ X41) != (k1_tarski @ X40)))),
% 0.67/0.86      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.67/0.86  thf('40', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.86         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.67/0.86          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['38', '39'])).
% 0.67/0.86  thf('41', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.67/0.86          | ((k1_xboole_0) != (k1_tarski @ X3)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['31', '40'])).
% 0.67/0.86  thf('42', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.67/0.86          | ((k1_xboole_0) != (k1_tarski @ X2)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['30', '41'])).
% 0.67/0.86  thf('43', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.67/0.86          | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['29', '42'])).
% 0.67/0.86  thf(d1_tarski, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.67/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.67/0.86  thf('44', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.86         (((X22) != (X21))
% 0.67/0.86          | (r2_hidden @ X22 @ X23)
% 0.67/0.86          | ((X23) != (k1_tarski @ X21)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d1_tarski])).
% 0.67/0.86  thf('45', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.67/0.86      inference('simplify', [status(thm)], ['44'])).
% 0.67/0.86  thf('46', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.67/0.86      inference('demod', [status(thm)], ['43', '45'])).
% 0.67/0.86  thf('47', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['26', '46'])).
% 0.67/0.86  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qe7AbJczTI

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:48 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 347 expanded)
%              Number of leaves         :   23 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  575 (3011 expanded)
%              Number of equality atoms :   69 ( 409 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X9: $i,X12: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X12 @ X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X25 ) @ ( k1_setfam_1 @ X26 ) ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X27: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('27',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','24'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('32',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_A @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','24'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_A @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','24'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','24'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_A @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','24'])).

thf('54',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','42','52','53'])).

thf('55',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qe7AbJczTI
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 209 iterations in 0.137s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(t69_enumset1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.55  thf('0', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.55  thf(d2_tarski, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.55         (((X10) != (X9))
% 0.36/0.55          | (r2_hidden @ X10 @ X11)
% 0.36/0.55          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X9 : $i, X12 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X12 @ X9))),
% 0.36/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.55  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['0', '2'])).
% 0.36/0.55  thf(t41_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k2_tarski @ A @ B ) =
% 0.36/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         ((k2_tarski @ X15 @ X16)
% 0.36/0.55           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.55  thf(t11_setfam_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.36/0.55  thf('5', plain, (![X27 : $i]: ((k1_setfam_1 @ (k1_tarski @ X27)) = (X27))),
% 0.36/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.36/0.55  thf(t10_setfam_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.55          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.36/0.55            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i]:
% 0.36/0.55         (((X25) = (k1_xboole_0))
% 0.36/0.55          | ((k1_setfam_1 @ (k2_xboole_0 @ X25 @ X26))
% 0.36/0.55              = (k3_xboole_0 @ (k1_setfam_1 @ X25) @ (k1_setfam_1 @ X26)))
% 0.36/0.55          | ((X26) = (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.36/0.55            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.36/0.55          | ((X1) = (k1_xboole_0))
% 0.36/0.55          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.36/0.55            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.36/0.55          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.36/0.55          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['4', '7'])).
% 0.36/0.55  thf('9', plain, (![X27 : $i]: ((k1_setfam_1 @ (k1_tarski @ X27)) = (X27))),
% 0.36/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.36/0.55          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.36/0.55          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf(t12_setfam_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.55         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.36/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.36/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.55  thf(t19_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.36/0.55       ( k1_tarski @ A ) ))).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k3_xboole_0 @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X24))
% 0.36/0.55           = (k1_tarski @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.36/0.55           = (k1_tarski @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.55  thf(d7_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.36/0.55          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.36/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.36/0.55           = (k1_tarski @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.55  thf(t4_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.36/0.55          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.36/0.55  thf('25', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.36/0.55  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['0', '2'])).
% 0.36/0.55  thf('27', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.36/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf('28', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.36/0.55  thf(t71_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.55         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.36/0.55           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.55  thf(t70_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]:
% 0.36/0.55         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.36/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k3_xboole_0 @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X24))
% 0.36/0.55           = (k1_tarski @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.36/0.55          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ (k1_tarski @ X1) @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ k1_xboole_0 @ 
% 0.36/0.55             (k2_enumset1 @ sk_A @ sk_A @ sk_A @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '35'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.55         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.36/0.55           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]:
% 0.36/0.55         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.36/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         ((k2_tarski @ X15 @ X16)
% 0.36/0.55           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k2_tarski @ sk_A @ X0)
% 0.36/0.55           = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('43', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k3_xboole_0 @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X24))
% 0.36/0.55           = (k1_tarski @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.36/0.55          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55          | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '46'])).
% 0.36/0.55  thf('48', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55          | (r1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k2_tarski @ sk_A @ X0)
% 0.36/0.55           = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.36/0.55          (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('53', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.36/0.55  thf('54', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.36/0.55      inference('demod', [status(thm)], ['36', '39', '42', '52', '53'])).
% 0.36/0.55  thf('55', plain, ($false), inference('sup-', [status(thm)], ['27', '54'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

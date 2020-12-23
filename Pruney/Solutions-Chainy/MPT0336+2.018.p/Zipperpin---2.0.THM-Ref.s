%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O4L14ILY1Y

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:22 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  516 ( 759 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k3_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k3_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('43',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['15','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['2','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O4L14ILY1Y
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.96/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.96/1.16  % Solved by: fo/fo7.sh
% 0.96/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.16  % done 1661 iterations in 0.704s
% 0.96/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.96/1.16  % SZS output start Refutation
% 0.96/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.96/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.16  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.96/1.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.96/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.96/1.16  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.96/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.96/1.16  thf(sk_D_type, type, sk_D: $i).
% 0.96/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.96/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.16  thf(t149_zfmisc_1, conjecture,
% 0.96/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.16     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.96/1.16         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.96/1.16       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.96/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.16    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.16        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.96/1.16            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.96/1.16          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.96/1.16    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.96/1.16  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf(commutativity_k2_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.96/1.16  thf('1', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.16      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.96/1.16  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.96/1.16      inference('demod', [status(thm)], ['0', '1'])).
% 0.96/1.16  thf(t4_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.96/1.16            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.96/1.16       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.96/1.16            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.96/1.16  thf('3', plain,
% 0.96/1.16      (![X13 : $i, X14 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X13 @ X14)
% 0.96/1.16          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.96/1.16  thf(l27_zfmisc_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.96/1.16  thf('4', plain,
% 0.96/1.16      (![X37 : $i, X38 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 0.96/1.16      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.96/1.16  thf('5', plain,
% 0.96/1.16      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf(commutativity_k3_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.96/1.16  thf('6', plain,
% 0.96/1.16      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.96/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.96/1.16  thf('7', plain,
% 0.96/1.16      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.96/1.16      inference('demod', [status(thm)], ['5', '6'])).
% 0.96/1.16  thf(t28_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.96/1.16  thf('8', plain,
% 0.96/1.16      (![X20 : $i, X21 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.96/1.16      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.96/1.16  thf('9', plain,
% 0.96/1.16      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.96/1.16         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.96/1.16      inference('sup-', [status(thm)], ['7', '8'])).
% 0.96/1.16  thf('10', plain,
% 0.96/1.16      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.96/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.96/1.16  thf('11', plain,
% 0.96/1.16      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.96/1.16         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.96/1.16      inference('demod', [status(thm)], ['9', '10'])).
% 0.96/1.16  thf('12', plain,
% 0.96/1.16      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.96/1.16          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.96/1.16      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.96/1.16  thf('13', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.96/1.16          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['11', '12'])).
% 0.96/1.16  thf('14', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.96/1.16          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['4', '13'])).
% 0.96/1.16  thf('15', plain,
% 0.96/1.16      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.96/1.16        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['3', '14'])).
% 0.96/1.16  thf('16', plain,
% 0.96/1.16      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.96/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.96/1.16  thf('17', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf(symmetry_r1_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.96/1.16  thf('18', plain,
% 0.96/1.16      (![X7 : $i, X8 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.96/1.16      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.96/1.16  thf('19', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.96/1.16      inference('sup-', [status(thm)], ['17', '18'])).
% 0.96/1.16  thf(d7_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.96/1.16       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.96/1.16  thf('20', plain,
% 0.96/1.16      (![X4 : $i, X5 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['19', '20'])).
% 0.96/1.16  thf(t16_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.96/1.16       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.96/1.16  thf('22', plain,
% 0.96/1.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19)
% 0.96/1.16           = (k3_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.96/1.16  thf('23', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.96/1.16           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_2 @ X0)))),
% 0.96/1.16      inference('sup+', [status(thm)], ['21', '22'])).
% 0.96/1.16  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.96/1.16  thf('24', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.96/1.16      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.96/1.16  thf('25', plain,
% 0.96/1.16      (![X7 : $i, X8 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.96/1.16      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.96/1.16  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.96/1.16      inference('sup-', [status(thm)], ['24', '25'])).
% 0.96/1.16  thf('27', plain,
% 0.96/1.16      (![X4 : $i, X5 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('28', plain,
% 0.96/1.16      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['26', '27'])).
% 0.96/1.16  thf('29', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_2 @ X0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['23', '28'])).
% 0.96/1.16  thf('30', plain,
% 0.96/1.16      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.96/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.96/1.16  thf('31', plain,
% 0.96/1.16      (![X4 : $i, X6 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('32', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.96/1.16      inference('sup-', [status(thm)], ['30', '31'])).
% 0.96/1.16  thf('33', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((k1_xboole_0) != (k1_xboole_0))
% 0.96/1.16          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B))),
% 0.96/1.16      inference('sup-', [status(thm)], ['29', '32'])).
% 0.96/1.16  thf('34', plain,
% 0.96/1.16      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B)),
% 0.96/1.16      inference('simplify', [status(thm)], ['33'])).
% 0.96/1.16  thf('35', plain,
% 0.96/1.16      (![X4 : $i, X5 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('36', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B) = (k1_xboole_0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['34', '35'])).
% 0.96/1.16  thf('37', plain,
% 0.96/1.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19)
% 0.96/1.16           = (k3_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.96/1.16  thf('38', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.96/1.16      inference('demod', [status(thm)], ['36', '37'])).
% 0.96/1.16  thf('39', plain,
% 0.96/1.16      (![X4 : $i, X6 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('40', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((k1_xboole_0) != (k1_xboole_0))
% 0.96/1.16          | (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['38', '39'])).
% 0.96/1.16  thf('41', plain,
% 0.96/1.16      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.96/1.16      inference('simplify', [status(thm)], ['40'])).
% 0.96/1.16  thf('42', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf(t3_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.96/1.16            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.96/1.16       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.96/1.16            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.96/1.16  thf('43', plain,
% 0.96/1.16      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X11 @ X9)
% 0.96/1.16          | ~ (r2_hidden @ X11 @ X12)
% 0.96/1.16          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.96/1.16      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.96/1.16  thf('44', plain,
% 0.96/1.16      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['42', '43'])).
% 0.96/1.16  thf('45', plain,
% 0.96/1.16      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.96/1.16      inference('sup-', [status(thm)], ['41', '44'])).
% 0.96/1.16  thf('46', plain,
% 0.96/1.16      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['16', '45'])).
% 0.96/1.16  thf('47', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.96/1.16      inference('sup-', [status(thm)], ['15', '46'])).
% 0.96/1.16  thf('48', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.96/1.16      inference('sup-', [status(thm)], ['17', '18'])).
% 0.96/1.16  thf(t70_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.96/1.16            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.96/1.16       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.96/1.16            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.96/1.16  thf('49', plain,
% 0.96/1.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 0.96/1.16          | ~ (r1_xboole_0 @ X23 @ X24)
% 0.96/1.16          | ~ (r1_xboole_0 @ X23 @ X25))),
% 0.96/1.16      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.96/1.16  thf('50', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.96/1.16          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['48', '49'])).
% 0.96/1.16  thf('51', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 0.96/1.16      inference('sup-', [status(thm)], ['47', '50'])).
% 0.96/1.16  thf('52', plain,
% 0.96/1.16      (![X7 : $i, X8 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.96/1.16      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.96/1.16  thf('53', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.96/1.16      inference('sup-', [status(thm)], ['51', '52'])).
% 0.96/1.16  thf('54', plain, ($false), inference('demod', [status(thm)], ['2', '53'])).
% 0.96/1.16  
% 0.96/1.16  % SZS output end Refutation
% 0.96/1.16  
% 0.96/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnZycO8TFc

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k3_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
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
    ! [X24: $i] :
      ( r1_xboole_0 @ X24 @ k1_xboole_0 ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k3_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ X27 ) ) ),
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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnZycO8TFc
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:36:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.80/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.01  % Solved by: fo/fo7.sh
% 0.80/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.01  % done 1416 iterations in 0.573s
% 0.80/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.01  % SZS output start Refutation
% 0.80/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.80/1.01  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.80/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.01  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.80/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.80/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.01  thf(t149_zfmisc_1, conjecture,
% 0.80/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.01     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.80/1.01         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.80/1.01       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.80/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.01        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.80/1.01            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.80/1.01          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.80/1.01    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.80/1.01  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(commutativity_k2_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.80/1.01  thf('1', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.80/1.01  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.80/1.01      inference('demod', [status(thm)], ['0', '1'])).
% 0.80/1.01  thf(t4_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.01            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.01       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.80/1.01            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.80/1.01  thf('3', plain,
% 0.80/1.01      (![X13 : $i, X14 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X13 @ X14)
% 0.80/1.01          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.01  thf(l27_zfmisc_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.80/1.01  thf('4', plain,
% 0.80/1.01      (![X37 : $i, X38 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 0.80/1.01      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.80/1.01  thf('5', plain,
% 0.80/1.01      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/1.01  thf('6', plain,
% 0.80/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.01  thf('7', plain,
% 0.80/1.01      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.80/1.01      inference('demod', [status(thm)], ['5', '6'])).
% 0.80/1.01  thf(t28_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.80/1.01  thf('8', plain,
% 0.80/1.01      (![X22 : $i, X23 : $i]:
% 0.80/1.01         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.80/1.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.80/1.01  thf('9', plain,
% 0.80/1.01      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.80/1.01         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.80/1.01  thf('10', plain,
% 0.80/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.01  thf('11', plain,
% 0.80/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.80/1.01         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.80/1.01  thf('12', plain,
% 0.80/1.01      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.80/1.01         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.80/1.01          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.80/1.01      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.01  thf('13', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.80/1.01          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['11', '12'])).
% 0.80/1.01  thf('14', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.80/1.01          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['4', '13'])).
% 0.80/1.01  thf('15', plain,
% 0.80/1.01      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.80/1.01        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['3', '14'])).
% 0.80/1.01  thf('16', plain,
% 0.80/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.01  thf('17', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(symmetry_r1_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.80/1.01  thf('18', plain,
% 0.80/1.01      (![X7 : $i, X8 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.80/1.01      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.80/1.01  thf('19', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.80/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.01  thf(d7_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.80/1.01       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.80/1.01  thf('20', plain,
% 0.80/1.01      (![X4 : $i, X5 : $i]:
% 0.80/1.01         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.80/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/1.01  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['19', '20'])).
% 0.80/1.01  thf(t16_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.80/1.01       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.80/1.01  thf('22', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.80/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21)
% 0.80/1.01           = (k3_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.80/1.01  thf('23', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.80/1.01           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_2 @ X0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['21', '22'])).
% 0.80/1.01  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.80/1.01  thf('24', plain, (![X24 : $i]: (r1_xboole_0 @ X24 @ k1_xboole_0)),
% 0.80/1.01      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.80/1.01  thf('25', plain,
% 0.80/1.01      (![X7 : $i, X8 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.80/1.01      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.80/1.01  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.80/1.01      inference('sup-', [status(thm)], ['24', '25'])).
% 0.80/1.01  thf('27', plain,
% 0.80/1.01      (![X4 : $i, X5 : $i]:
% 0.80/1.01         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.80/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/1.01  thf('28', plain,
% 0.80/1.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.80/1.01  thf('29', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_2 @ X0)))),
% 0.80/1.01      inference('demod', [status(thm)], ['23', '28'])).
% 0.80/1.01  thf('30', plain,
% 0.80/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.01  thf('31', plain,
% 0.80/1.01      (![X4 : $i, X6 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.80/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/1.01  thf('32', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.80/1.01      inference('sup-', [status(thm)], ['30', '31'])).
% 0.80/1.01  thf('33', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (((k1_xboole_0) != (k1_xboole_0))
% 0.80/1.01          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B))),
% 0.80/1.01      inference('sup-', [status(thm)], ['29', '32'])).
% 0.80/1.01  thf('34', plain,
% 0.80/1.01      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B)),
% 0.80/1.01      inference('simplify', [status(thm)], ['33'])).
% 0.80/1.01  thf('35', plain,
% 0.80/1.01      (![X4 : $i, X5 : $i]:
% 0.80/1.01         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.80/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/1.01  thf('36', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B) = (k1_xboole_0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.80/1.01  thf('37', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.80/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21)
% 0.80/1.01           = (k3_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.80/1.01  thf('38', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k3_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.80/1.01  thf('39', plain,
% 0.80/1.01      (![X4 : $i, X6 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.80/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/1.01  thf('40', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (((k1_xboole_0) != (k1_xboole_0))
% 0.80/1.01          | (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['38', '39'])).
% 0.80/1.01  thf('41', plain,
% 0.80/1.01      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.80/1.01      inference('simplify', [status(thm)], ['40'])).
% 0.80/1.01  thf('42', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(t3_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.80/1.01            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.01       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.80/1.01            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.80/1.01  thf('43', plain,
% 0.80/1.01      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.80/1.01         (~ (r2_hidden @ X11 @ X9)
% 0.80/1.01          | ~ (r2_hidden @ X11 @ X12)
% 0.80/1.01          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.80/1.01      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.80/1.01  thf('44', plain,
% 0.80/1.01      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['42', '43'])).
% 0.80/1.01  thf('45', plain,
% 0.80/1.01      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.80/1.01      inference('sup-', [status(thm)], ['41', '44'])).
% 0.80/1.01  thf('46', plain,
% 0.80/1.01      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['16', '45'])).
% 0.80/1.01  thf('47', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.80/1.01      inference('sup-', [status(thm)], ['15', '46'])).
% 0.80/1.01  thf('48', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.80/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.01  thf(t70_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.80/1.01            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.80/1.01       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.80/1.01            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.80/1.01  thf('49', plain,
% 0.80/1.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 0.80/1.01          | ~ (r1_xboole_0 @ X25 @ X26)
% 0.80/1.01          | ~ (r1_xboole_0 @ X25 @ X27))),
% 0.80/1.01      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.80/1.01  thf('50', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.80/1.01          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('51', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['47', '50'])).
% 0.80/1.01  thf('52', plain,
% 0.80/1.01      (![X7 : $i, X8 : $i]:
% 0.80/1.01         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.80/1.01      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.80/1.01  thf('53', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.80/1.01      inference('sup-', [status(thm)], ['51', '52'])).
% 0.80/1.01  thf('54', plain, ($false), inference('demod', [status(thm)], ['2', '53'])).
% 0.80/1.01  
% 0.80/1.01  % SZS output end Refutation
% 0.80/1.01  
% 0.80/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

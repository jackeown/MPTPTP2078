%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9IyMBejGcl

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:07 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 128 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  487 ( 882 expanded)
%              Number of equality atoms :   46 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_3 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['3','30'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_3 ) ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','40'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9IyMBejGcl
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 418 iterations in 0.198s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(t73_xboole_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.45/0.64       ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ C ) ) =>
% 0.45/0.64          ( r1_tarski @ A @ B ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.45/0.64  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_3))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t12_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i]:
% 0.45/0.64         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_3))
% 0.45/0.64         = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf(t3_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.64  thf('4', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf(t48_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 0.45/0.64           = (k3_xboole_0 @ X27 @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(t3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.64            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.64  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C_3)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d7_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_C_3) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf(t4_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.45/0.64          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_A @ sk_C_3))),
% 0.45/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_C_3)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '14'])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '17'])).
% 0.45/0.64  thf(t41_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.64       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.45/0.64           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.64           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.64  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('23', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.64  thf(t47_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26))
% 0.45/0.64           = (k4_xboole_0 @ X25 @ X26))),
% 0.45/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.64           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['20', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_3)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['3', '30'])).
% 0.45/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.64  thf('33', plain, (((k3_xboole_0 @ sk_A @ sk_C_3) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26))
% 0.45/0.64           = (k4_xboole_0 @ X25 @ X26))),
% 0.45/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.45/0.64      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf('37', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.45/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.45/0.64           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_A @ X0)
% 0.45/0.64           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_3 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_A @ X0)
% 0.45/0.64           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_3)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['32', '39'])).
% 0.45/0.64  thf('41', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '40'])).
% 0.45/0.64  thf(t39_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X19 : $i, X20 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.45/0.64           = (k2_xboole_0 @ X19 @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf(d3_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X3 : $i, X5 : $i]:
% 0.45/0.64         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i]:
% 0.45/0.64         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.64  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.64  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.64  thf('51', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '50'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.64  thf(t7_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['52', '53'])).
% 0.45/0.64  thf('55', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.64      inference('sup+', [status(thm)], ['51', '54'])).
% 0.45/0.64  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

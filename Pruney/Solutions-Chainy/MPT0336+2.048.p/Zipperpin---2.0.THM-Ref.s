%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f0xy473qEO

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:26 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 106 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   21
%              Number of atoms          :  505 ( 781 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
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
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','45'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf('48',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f0xy473qEO
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.85  % Solved by: fo/fo7.sh
% 0.58/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.85  % done 765 iterations in 0.394s
% 0.58/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.85  % SZS output start Refutation
% 0.58/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.85  thf(t149_zfmisc_1, conjecture,
% 0.58/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.85     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.58/0.85         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.58/0.85       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.58/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.85    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.85        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.58/0.85            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.58/0.85          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.58/0.85    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.58/0.85  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf(d7_xboole_0, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.58/0.85       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.85  thf('2', plain,
% 0.58/0.85      (![X2 : $i, X3 : $i]:
% 0.58/0.85         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.85  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.85  thf('4', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.85  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.58/0.85      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.85  thf('6', plain,
% 0.58/0.85      (![X2 : $i, X4 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('7', plain,
% 0.58/0.85      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.58/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.85  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.58/0.85      inference('simplify', [status(thm)], ['7'])).
% 0.58/0.85  thf(l27_zfmisc_1, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.58/0.85  thf('9', plain,
% 0.58/0.85      (![X27 : $i, X28 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.58/0.85      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.58/0.85  thf('10', plain,
% 0.58/0.85      (![X2 : $i, X3 : $i]:
% 0.58/0.85         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('11', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r2_hidden @ X1 @ X0)
% 0.58/0.85          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.85  thf('12', plain,
% 0.58/0.85      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('13', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.85  thf('14', plain,
% 0.58/0.85      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.58/0.85      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.85  thf(t28_xboole_1, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.85  thf('15', plain,
% 0.58/0.85      (![X14 : $i, X15 : $i]:
% 0.58/0.85         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.58/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.85  thf('16', plain,
% 0.58/0.85      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.58/0.85         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.58/0.85      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.85  thf('17', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.85  thf('18', plain,
% 0.58/0.85      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.58/0.85         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.58/0.85      inference('demod', [status(thm)], ['16', '17'])).
% 0.58/0.85  thf('19', plain,
% 0.58/0.85      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.58/0.85        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.58/0.85      inference('sup+', [status(thm)], ['11', '18'])).
% 0.58/0.85  thf('20', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.85  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.58/0.85      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.85  thf(t16_xboole_1, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.85       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.58/0.85  thf('22', plain,
% 0.58/0.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.85         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.58/0.85           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.58/0.85  thf('23', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.85           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.58/0.85      inference('sup+', [status(thm)], ['21', '22'])).
% 0.58/0.85  thf('24', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.85  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.58/0.85  thf('25', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.58/0.85      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.58/0.85  thf('26', plain,
% 0.58/0.85      (![X2 : $i, X3 : $i]:
% 0.58/0.85         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('27', plain,
% 0.58/0.85      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.85  thf('28', plain,
% 0.58/0.85      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.85      inference('sup+', [status(thm)], ['24', '27'])).
% 0.58/0.85  thf('29', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.58/0.85      inference('demod', [status(thm)], ['23', '28'])).
% 0.58/0.85  thf('30', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.85  thf('31', plain,
% 0.58/0.85      (![X2 : $i, X4 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('32', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.85      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.85  thf('33', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.85          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 0.58/0.85      inference('sup-', [status(thm)], ['29', '32'])).
% 0.58/0.85  thf('34', plain,
% 0.58/0.85      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 0.58/0.85      inference('simplify', [status(thm)], ['33'])).
% 0.58/0.85  thf('35', plain,
% 0.58/0.85      (![X2 : $i, X3 : $i]:
% 0.58/0.85         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('36', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B) = (k1_xboole_0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.85  thf('37', plain,
% 0.58/0.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.85         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.58/0.85           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.58/0.85  thf('38', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.58/0.85      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.85  thf('39', plain,
% 0.58/0.85      (![X2 : $i, X4 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('40', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.85          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.85  thf('41', plain,
% 0.58/0.85      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.58/0.85      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.85  thf('42', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf(t3_xboole_0, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.58/0.85            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.85       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.85            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.58/0.85  thf('43', plain,
% 0.58/0.85      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X9 @ X7)
% 0.58/0.85          | ~ (r2_hidden @ X9 @ X10)
% 0.58/0.85          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.58/0.85      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.85  thf('44', plain,
% 0.58/0.85      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.85  thf('45', plain,
% 0.58/0.85      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.58/0.85      inference('sup-', [status(thm)], ['41', '44'])).
% 0.58/0.85  thf('46', plain,
% 0.58/0.85      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['20', '45'])).
% 0.58/0.85  thf('47', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.58/0.85      inference('sup-', [status(thm)], ['19', '46'])).
% 0.58/0.85  thf('48', plain,
% 0.58/0.85      (![X2 : $i, X4 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.58/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.85  thf('49', plain,
% 0.58/0.85      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.58/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.85  thf('50', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.58/0.85      inference('simplify', [status(thm)], ['49'])).
% 0.58/0.85  thf(t70_xboole_1, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.58/0.85            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.58/0.85       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.58/0.85            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.58/0.85  thf('51', plain,
% 0.58/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.58/0.85          | ~ (r1_xboole_0 @ X17 @ X18)
% 0.58/0.85          | ~ (r1_xboole_0 @ X17 @ X19))),
% 0.58/0.85      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.58/0.85  thf('52', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.58/0.85          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.85  thf('53', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.58/0.85      inference('sup-', [status(thm)], ['8', '52'])).
% 0.58/0.85  thf(symmetry_r1_xboole_0, axiom,
% 0.58/0.85    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.58/0.85  thf('54', plain,
% 0.58/0.85      (![X5 : $i, X6 : $i]:
% 0.58/0.85         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.58/0.85      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.58/0.85  thf('55', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.58/0.85      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.85  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.58/0.85  
% 0.58/0.85  % SZS output end Refutation
% 0.58/0.85  
% 0.69/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

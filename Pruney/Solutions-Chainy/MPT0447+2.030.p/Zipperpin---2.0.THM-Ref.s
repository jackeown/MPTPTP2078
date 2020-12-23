%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oIXsY1L3S9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:56 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 133 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (1017 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( r1_tarski @ ( k2_relat_1 @ X57 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( r1_tarski @ X57 @ X56 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('26',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X52 @ X54 )
      | ( r1_tarski @ ( k1_setfam_1 @ X53 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( r1_tarski @ ( k1_relat_1 @ X57 ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( r1_tarski @ X57 @ X56 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oIXsY1L3S9
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:56:03 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.19/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.39  % Solved by: fo/fo7.sh
% 1.19/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.39  % done 2798 iterations in 0.950s
% 1.19/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.39  % SZS output start Refutation
% 1.19/1.39  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.19/1.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.19/1.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.19/1.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.19/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.39  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.19/1.39  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.19/1.39  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.19/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.39  thf(t31_relat_1, conjecture,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( v1_relat_1 @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( v1_relat_1 @ B ) =>
% 1.19/1.39           ( ( r1_tarski @ A @ B ) =>
% 1.19/1.39             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.39    (~( ![A:$i]:
% 1.19/1.39        ( ( v1_relat_1 @ A ) =>
% 1.19/1.39          ( ![B:$i]:
% 1.19/1.39            ( ( v1_relat_1 @ B ) =>
% 1.19/1.39              ( ( r1_tarski @ A @ B ) =>
% 1.19/1.39                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.19/1.39    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.19/1.39  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(d6_relat_1, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( v1_relat_1 @ A ) =>
% 1.19/1.39       ( ( k3_relat_1 @ A ) =
% 1.19/1.39         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.19/1.39  thf('1', plain,
% 1.19/1.39      (![X55 : $i]:
% 1.19/1.39         (((k3_relat_1 @ X55)
% 1.19/1.39            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 1.19/1.39          | ~ (v1_relat_1 @ X55))),
% 1.19/1.39      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.19/1.39  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t25_relat_1, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( v1_relat_1 @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( v1_relat_1 @ B ) =>
% 1.19/1.39           ( ( r1_tarski @ A @ B ) =>
% 1.19/1.39             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.19/1.39               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.19/1.39  thf('3', plain,
% 1.19/1.39      (![X56 : $i, X57 : $i]:
% 1.19/1.39         (~ (v1_relat_1 @ X56)
% 1.19/1.39          | (r1_tarski @ (k2_relat_1 @ X57) @ (k2_relat_1 @ X56))
% 1.19/1.39          | ~ (r1_tarski @ X57 @ X56)
% 1.19/1.39          | ~ (v1_relat_1 @ X57))),
% 1.19/1.39      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.19/1.39  thf('4', plain,
% 1.19/1.39      ((~ (v1_relat_1 @ sk_A)
% 1.19/1.39        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.19/1.39        | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['2', '3'])).
% 1.19/1.39  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('7', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.19/1.39  thf(t28_xboole_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.19/1.39  thf('8', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 1.19/1.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.39  thf('9', plain,
% 1.19/1.39      (((k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.19/1.39         = (k2_relat_1 @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.39  thf('10', plain,
% 1.19/1.39      (![X55 : $i]:
% 1.19/1.39         (((k3_relat_1 @ X55)
% 1.19/1.39            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 1.19/1.39          | ~ (v1_relat_1 @ X55))),
% 1.19/1.39      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.19/1.39  thf(commutativity_k2_tarski, axiom,
% 1.19/1.39    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.19/1.39  thf('11', plain,
% 1.19/1.39      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 1.19/1.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.19/1.39  thf(l51_zfmisc_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.39  thf('12', plain,
% 1.19/1.39      (![X48 : $i, X49 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('13', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['11', '12'])).
% 1.19/1.39  thf('14', plain,
% 1.19/1.39      (![X48 : $i, X49 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('15', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['13', '14'])).
% 1.19/1.39  thf(t7_xboole_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.39  thf('16', plain,
% 1.19/1.39      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 1.19/1.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.19/1.39  thf('17', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['15', '16'])).
% 1.19/1.39  thf('18', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.19/1.39          | ~ (v1_relat_1 @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['10', '17'])).
% 1.19/1.39  thf(t70_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.19/1.39  thf('19', plain,
% 1.19/1.39      (![X21 : $i, X22 : $i]:
% 1.19/1.39         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 1.19/1.39      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.19/1.39  thf(d1_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.39     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.19/1.39       ( ![E:$i]:
% 1.19/1.39         ( ( r2_hidden @ E @ D ) <=>
% 1.19/1.39           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.19/1.39  thf(zf_stmt_2, axiom,
% 1.19/1.39    (![E:$i,C:$i,B:$i,A:$i]:
% 1.19/1.39     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.19/1.39       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_3, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.39     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.19/1.39       ( ![E:$i]:
% 1.19/1.39         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.19/1.39  thf('20', plain,
% 1.19/1.39      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.39         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 1.19/1.39          | (r2_hidden @ X14 @ X18)
% 1.19/1.39          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.39  thf('21', plain,
% 1.19/1.39      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.19/1.39         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 1.19/1.39          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 1.19/1.39      inference('simplify', [status(thm)], ['20'])).
% 1.19/1.39  thf('22', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.19/1.39          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['19', '21'])).
% 1.19/1.39  thf('23', plain,
% 1.19/1.39      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.19/1.39         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.19/1.39  thf('24', plain,
% 1.19/1.39      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 1.19/1.39      inference('simplify', [status(thm)], ['23'])).
% 1.19/1.39  thf('25', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.19/1.39      inference('sup-', [status(thm)], ['22', '24'])).
% 1.19/1.39  thf(t8_setfam_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.19/1.39       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 1.19/1.39  thf('26', plain,
% 1.19/1.39      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X52 @ X53)
% 1.19/1.39          | ~ (r1_tarski @ X52 @ X54)
% 1.19/1.39          | (r1_tarski @ (k1_setfam_1 @ X53) @ X54))),
% 1.19/1.39      inference('cnf', [status(esa)], [t8_setfam_1])).
% 1.19/1.39  thf('27', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 1.19/1.39          | ~ (r1_tarski @ X1 @ X2))),
% 1.19/1.39      inference('sup-', [status(thm)], ['25', '26'])).
% 1.19/1.39  thf('28', plain,
% 1.19/1.39      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 1.19/1.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.19/1.39  thf(t12_setfam_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.19/1.39  thf('29', plain,
% 1.19/1.39      (![X50 : $i, X51 : $i]:
% 1.19/1.39         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 1.19/1.39      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.19/1.39  thf('30', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['28', '29'])).
% 1.19/1.39  thf('31', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X1 @ X2))),
% 1.19/1.39      inference('demod', [status(thm)], ['27', '30'])).
% 1.19/1.39  thf('32', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (~ (v1_relat_1 @ X0)
% 1.19/1.39          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ 
% 1.19/1.39             (k3_relat_1 @ X0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['18', '31'])).
% 1.19/1.39  thf('33', plain,
% 1.19/1.39      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.19/1.39        | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.39      inference('sup+', [status(thm)], ['9', '32'])).
% 1.19/1.39  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['33', '34'])).
% 1.19/1.39  thf('36', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('37', plain,
% 1.19/1.39      (![X56 : $i, X57 : $i]:
% 1.19/1.39         (~ (v1_relat_1 @ X56)
% 1.19/1.39          | (r1_tarski @ (k1_relat_1 @ X57) @ (k1_relat_1 @ X56))
% 1.19/1.39          | ~ (r1_tarski @ X57 @ X56)
% 1.19/1.39          | ~ (v1_relat_1 @ X57))),
% 1.19/1.39      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.19/1.39  thf('38', plain,
% 1.19/1.39      ((~ (v1_relat_1 @ sk_A)
% 1.19/1.39        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.19/1.39        | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['36', '37'])).
% 1.19/1.39  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('41', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.19/1.39  thf('42', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 1.19/1.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.39  thf('43', plain,
% 1.19/1.39      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.19/1.39         = (k1_relat_1 @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['41', '42'])).
% 1.19/1.39  thf('44', plain,
% 1.19/1.39      (![X55 : $i]:
% 1.19/1.39         (((k3_relat_1 @ X55)
% 1.19/1.39            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 1.19/1.39          | ~ (v1_relat_1 @ X55))),
% 1.19/1.39      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.19/1.39  thf('45', plain,
% 1.19/1.39      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 1.19/1.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.19/1.39  thf('46', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.19/1.39          | ~ (v1_relat_1 @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['44', '45'])).
% 1.19/1.39  thf('47', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X1 @ X2))),
% 1.19/1.39      inference('demod', [status(thm)], ['27', '30'])).
% 1.19/1.39  thf('48', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (~ (v1_relat_1 @ X0)
% 1.19/1.39          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.19/1.39             (k3_relat_1 @ X0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['46', '47'])).
% 1.19/1.39  thf('49', plain,
% 1.19/1.39      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.19/1.39        | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.39      inference('sup+', [status(thm)], ['43', '48'])).
% 1.19/1.39  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['49', '50'])).
% 1.19/1.39  thf(t8_xboole_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.19/1.39       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.19/1.39  thf('52', plain,
% 1.19/1.39      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.19/1.39         (~ (r1_tarski @ X4 @ X5)
% 1.19/1.39          | ~ (r1_tarski @ X6 @ X5)
% 1.19/1.39          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.19/1.39  thf('53', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.19/1.39           (k3_relat_1 @ sk_B))
% 1.19/1.39          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['51', '52'])).
% 1.19/1.39  thf('54', plain,
% 1.19/1.39      ((r1_tarski @ 
% 1.19/1.39        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.19/1.39        (k3_relat_1 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['35', '53'])).
% 1.19/1.39  thf('55', plain,
% 1.19/1.39      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.19/1.39        | ~ (v1_relat_1 @ sk_A))),
% 1.19/1.39      inference('sup+', [status(thm)], ['1', '54'])).
% 1.19/1.39  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('57', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['55', '56'])).
% 1.19/1.39  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 1.19/1.39  
% 1.19/1.39  % SZS output end Refutation
% 1.19/1.39  
% 1.19/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

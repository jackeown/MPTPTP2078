%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vGGb29PiBm

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:31 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 125 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  577 ( 904 expanded)
%              Number of equality atoms :   56 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X40 @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ X24 )
      | ( ( k4_xboole_0 @ X22 @ X24 )
       != X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('42',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ ( k2_tarski @ X40 @ X42 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

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

thf('44',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('55',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != sk_B ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vGGb29PiBm
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 1255 iterations in 0.477s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.93  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(t48_zfmisc_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.75/0.93       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.93        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.75/0.93          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.75/0.93  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t38_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.75/0.93       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.75/0.93         ((r1_tarski @ (k2_tarski @ X40 @ X42) @ X43)
% 0.75/0.93          | ~ (r2_hidden @ X42 @ X43)
% 0.75/0.93          | ~ (r2_hidden @ X40 @ X43))),
% 0.75/0.93      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X0 @ sk_B)
% 0.75/0.93          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_A) @ sk_B)),
% 0.75/0.93      inference('sup-', [status(thm)], ['0', '3'])).
% 0.75/0.93  thf(commutativity_k2_tarski, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X27 : $i, X28 : $i]:
% 0.75/0.93         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.75/0.93  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf(t28_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (![X18 : $i, X19 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.75/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 0.75/0.93         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.93  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1))
% 0.75/0.93         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.75/0.93      inference('demod', [status(thm)], ['8', '9'])).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf(t100_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X15 : $i, X16 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X15 @ X16)
% 0.75/0.93           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X0 @ X1)
% 0.75/0.93           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['11', '12'])).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 0.75/0.93         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 0.75/0.93            (k2_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['10', '13'])).
% 0.75/0.93  thf(d5_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.93       ( ![D:$i]:
% 0.75/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.93           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.75/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.93          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.75/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.75/0.93          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.75/0.93          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.75/0.93          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.93  thf(d10_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.93  thf('19', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.75/0.93      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X18 : $i, X19 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.75/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.93  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (![X15 : $i, X16 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X15 @ X16)
% 0.75/0.93           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.75/0.93          | ((X1) = (k5_xboole_0 @ X0 @ X0))
% 0.75/0.93          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.75/0.93          | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 0.75/0.93      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((X1) = (k5_xboole_0 @ X0 @ X0))
% 0.75/0.93          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.75/0.93      inference('simplify', [status(thm)], ['25'])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X27 : $i, X28 : $i]:
% 0.75/0.93         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.75/0.93  thf(l51_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      (![X38 : $i, X39 : $i]:
% 0.75/0.93         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.75/0.93      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('sup+', [status(thm)], ['27', '28'])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (![X38 : $i, X39 : $i]:
% 0.75/0.93         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.75/0.93      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('sup+', [status(thm)], ['29', '30'])).
% 0.75/0.93  thf(t1_boole, axiom,
% 0.75/0.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.93  thf('32', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.93  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['31', '32'])).
% 0.75/0.93  thf(t39_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (![X20 : $i, X21 : $i]:
% 0.75/0.93         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.75/0.93           = (k2_xboole_0 @ X20 @ X21))),
% 0.75/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['33', '34'])).
% 0.75/0.93  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['31', '32'])).
% 0.75/0.93  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.93      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.93  thf(t83_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      (![X22 : $i, X24 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X22 @ X24) | ((k4_xboole_0 @ X22 @ X24) != (X22)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.93  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.75/0.93      inference('simplify', [status(thm)], ['39'])).
% 0.75/0.93  thf('41', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.75/0.93      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.75/0.93         ((r2_hidden @ X40 @ X41)
% 0.75/0.93          | ~ (r1_tarski @ (k2_tarski @ X40 @ X42) @ X41))),
% 0.75/0.93      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.75/0.93  thf('43', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['41', '42'])).
% 0.75/0.93  thf(t3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X10 @ X8)
% 0.75/0.93          | ~ (r2_hidden @ X10 @ X11)
% 0.75/0.93          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.75/0.93          | ~ (r2_hidden @ X1 @ X2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['43', '44'])).
% 0.75/0.93  thf('46', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.75/0.93      inference('sup-', [status(thm)], ['40', '45'])).
% 0.75/0.93  thf('47', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['26', '46'])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) = (k1_xboole_0))),
% 0.75/0.93      inference('demod', [status(thm)], ['14', '47'])).
% 0.75/0.93  thf('49', plain,
% 0.75/0.93      (![X20 : $i, X21 : $i]:
% 0.75/0.93         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.75/0.93           = (k2_xboole_0 @ X20 @ X21))),
% 0.75/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.75/0.93         = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.93  thf('51', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.93      inference('demod', [status(thm)], ['50', '51'])).
% 0.75/0.93  thf('53', plain,
% 0.75/0.93      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) != (sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('sup+', [status(thm)], ['29', '30'])).
% 0.75/0.93  thf('55', plain,
% 0.75/0.93      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) != (sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['53', '54'])).
% 0.75/0.93  thf('56', plain, ($false),
% 0.75/0.93      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

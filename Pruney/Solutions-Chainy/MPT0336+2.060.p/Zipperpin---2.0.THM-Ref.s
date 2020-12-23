%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r4S8bRGu0j

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:28 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 133 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 (1126 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
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
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
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
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['16','23'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['33','34','35','42'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r4S8bRGu0j
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:04:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.36/3.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.36/3.54  % Solved by: fo/fo7.sh
% 3.36/3.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.36/3.54  % done 3023 iterations in 3.063s
% 3.36/3.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.36/3.54  % SZS output start Refutation
% 3.36/3.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.36/3.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.36/3.54  thf(sk_D_type, type, sk_D: $i).
% 3.36/3.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.36/3.54  thf(sk_A_type, type, sk_A: $i).
% 3.36/3.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.36/3.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.36/3.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.36/3.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.36/3.54  thf(sk_B_type, type, sk_B: $i).
% 3.36/3.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.36/3.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.36/3.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.36/3.54  thf(t149_zfmisc_1, conjecture,
% 3.36/3.54    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.54     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.36/3.54         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.36/3.54       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.36/3.54  thf(zf_stmt_0, negated_conjecture,
% 3.36/3.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.54        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.36/3.54            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.36/3.54          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 3.36/3.54    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 3.36/3.54  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 3.36/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.54  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 3.36/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.54  thf(d7_xboole_0, axiom,
% 3.36/3.54    (![A:$i,B:$i]:
% 3.36/3.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.36/3.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.36/3.54  thf('2', plain,
% 3.36/3.54      (![X2 : $i, X3 : $i]:
% 3.36/3.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.36/3.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.36/3.54  thf('3', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['1', '2'])).
% 3.36/3.54  thf(commutativity_k3_xboole_0, axiom,
% 3.36/3.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.36/3.54  thf('4', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.36/3.54  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 3.36/3.54      inference('demod', [status(thm)], ['3', '4'])).
% 3.36/3.54  thf(l27_zfmisc_1, axiom,
% 3.36/3.54    (![A:$i,B:$i]:
% 3.36/3.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.36/3.54  thf('6', plain,
% 3.36/3.54      (![X27 : $i, X28 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 3.36/3.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 3.36/3.54  thf('7', plain,
% 3.36/3.54      (![X2 : $i, X3 : $i]:
% 3.36/3.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.36/3.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.36/3.54  thf('8', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]:
% 3.36/3.54         ((r2_hidden @ X1 @ X0)
% 3.36/3.54          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 3.36/3.54      inference('sup-', [status(thm)], ['6', '7'])).
% 3.36/3.54  thf('9', plain,
% 3.36/3.54      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 3.36/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.54  thf('10', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.36/3.54  thf('11', plain,
% 3.36/3.54      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 3.36/3.54      inference('demod', [status(thm)], ['9', '10'])).
% 3.36/3.54  thf(t28_xboole_1, axiom,
% 3.36/3.54    (![A:$i,B:$i]:
% 3.36/3.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.36/3.54  thf('12', plain,
% 3.36/3.54      (![X13 : $i, X14 : $i]:
% 3.36/3.54         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 3.36/3.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.36/3.54  thf('13', plain,
% 3.36/3.54      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 3.36/3.54         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.36/3.54      inference('sup-', [status(thm)], ['11', '12'])).
% 3.36/3.54  thf('14', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.36/3.54  thf('15', plain,
% 3.36/3.54      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 3.36/3.54         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.36/3.54      inference('demod', [status(thm)], ['13', '14'])).
% 3.36/3.54  thf('16', plain,
% 3.36/3.54      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 3.36/3.54        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 3.36/3.54      inference('sup+', [status(thm)], ['8', '15'])).
% 3.36/3.54  thf('17', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 3.36/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.54  thf(t74_xboole_1, axiom,
% 3.36/3.54    (![A:$i,B:$i,C:$i]:
% 3.36/3.54     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 3.36/3.54          ( r1_xboole_0 @ A @ B ) ) ))).
% 3.36/3.54  thf('18', plain,
% 3.36/3.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.36/3.54         (~ (r1_xboole_0 @ X15 @ X16)
% 3.36/3.54          | (r1_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 3.36/3.54      inference('cnf', [status(esa)], [t74_xboole_1])).
% 3.36/3.54  thf('19', plain,
% 3.36/3.54      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_B @ X0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['17', '18'])).
% 3.36/3.54  thf('20', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 3.36/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.54  thf(t3_xboole_0, axiom,
% 3.36/3.54    (![A:$i,B:$i]:
% 3.36/3.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.36/3.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.36/3.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.36/3.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.36/3.54  thf('21', plain,
% 3.36/3.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 3.36/3.54         (~ (r2_hidden @ X7 @ X5)
% 3.36/3.54          | ~ (r2_hidden @ X7 @ X8)
% 3.36/3.54          | ~ (r1_xboole_0 @ X5 @ X8))),
% 3.36/3.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.36/3.54  thf('22', plain,
% 3.36/3.54      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['20', '21'])).
% 3.36/3.54  thf('23', plain,
% 3.36/3.54      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['19', '22'])).
% 3.36/3.54  thf('24', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.36/3.54      inference('clc', [status(thm)], ['16', '23'])).
% 3.36/3.54  thf('25', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.36/3.54  thf(t4_xboole_0, axiom,
% 3.36/3.54    (![A:$i,B:$i]:
% 3.36/3.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 3.36/3.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.36/3.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.36/3.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 3.36/3.54  thf('26', plain,
% 3.36/3.54      (![X9 : $i, X10 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ X9 @ X10)
% 3.36/3.54          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 3.36/3.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.36/3.54  thf('27', plain,
% 3.36/3.54      (![X9 : $i, X10 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ X9 @ X10)
% 3.36/3.54          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 3.36/3.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.36/3.54  thf('28', plain,
% 3.36/3.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 3.36/3.54         (~ (r2_hidden @ X7 @ X5)
% 3.36/3.54          | ~ (r2_hidden @ X7 @ X8)
% 3.36/3.54          | ~ (r1_xboole_0 @ X5 @ X8))),
% 3.36/3.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.36/3.54  thf('29', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ X1 @ X0)
% 3.36/3.54          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.36/3.54          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 3.36/3.54      inference('sup-', [status(thm)], ['27', '28'])).
% 3.36/3.54  thf('30', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ X1 @ X0)
% 3.36/3.54          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.36/3.54          | (r1_xboole_0 @ X1 @ X0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['26', '29'])).
% 3.36/3.54  thf('31', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]:
% 3.36/3.54         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.36/3.54          | (r1_xboole_0 @ X1 @ X0))),
% 3.36/3.54      inference('simplify', [status(thm)], ['30'])).
% 3.36/3.54  thf('32', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]:
% 3.36/3.54         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 3.36/3.54          | (r1_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('sup-', [status(thm)], ['25', '31'])).
% 3.36/3.54  thf('33', plain,
% 3.36/3.54      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 3.36/3.54        | (r1_xboole_0 @ sk_B @ sk_A))),
% 3.36/3.54      inference('sup-', [status(thm)], ['24', '32'])).
% 3.36/3.54  thf('34', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.36/3.54  thf('35', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.36/3.54      inference('clc', [status(thm)], ['16', '23'])).
% 3.36/3.54  thf('36', plain,
% 3.36/3.54      (![X5 : $i, X6 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 3.36/3.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.36/3.54  thf('37', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['1', '2'])).
% 3.36/3.54  thf('38', plain,
% 3.36/3.54      (![X9 : $i, X11 : $i, X12 : $i]:
% 3.36/3.54         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 3.36/3.54          | ~ (r1_xboole_0 @ X9 @ X12))),
% 3.36/3.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.36/3.54  thf('39', plain,
% 3.36/3.54      (![X0 : $i]:
% 3.36/3.54         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 3.36/3.54      inference('sup-', [status(thm)], ['37', '38'])).
% 3.36/3.54  thf('40', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 3.36/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.54  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.36/3.54      inference('demod', [status(thm)], ['39', '40'])).
% 3.36/3.54  thf('42', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.36/3.54      inference('sup-', [status(thm)], ['36', '41'])).
% 3.36/3.54  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 3.36/3.54      inference('demod', [status(thm)], ['33', '34', '35', '42'])).
% 3.36/3.54  thf(t78_xboole_1, axiom,
% 3.36/3.54    (![A:$i,B:$i,C:$i]:
% 3.36/3.54     ( ( r1_xboole_0 @ A @ B ) =>
% 3.36/3.54       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 3.36/3.54         ( k3_xboole_0 @ A @ C ) ) ))).
% 3.36/3.54  thf('44', plain,
% 3.36/3.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.36/3.54         (~ (r1_xboole_0 @ X18 @ X19)
% 3.36/3.54          | ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 3.36/3.54              = (k3_xboole_0 @ X18 @ X20)))),
% 3.36/3.54      inference('cnf', [status(esa)], [t78_xboole_1])).
% 3.36/3.54  thf('45', plain,
% 3.36/3.54      (![X0 : $i]:
% 3.36/3.54         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 3.36/3.54           = (k3_xboole_0 @ sk_B @ X0))),
% 3.36/3.54      inference('sup-', [status(thm)], ['43', '44'])).
% 3.36/3.54  thf('46', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.36/3.54  thf('47', plain,
% 3.36/3.54      (![X2 : $i, X4 : $i]:
% 3.36/3.54         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.36/3.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.36/3.54  thf('48', plain,
% 3.36/3.54      (![X0 : $i, X1 : $i]:
% 3.36/3.54         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 3.36/3.54      inference('sup-', [status(thm)], ['46', '47'])).
% 3.36/3.54  thf('49', plain,
% 3.36/3.54      (![X0 : $i]:
% 3.36/3.54         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 3.36/3.54          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.36/3.54      inference('sup-', [status(thm)], ['45', '48'])).
% 3.36/3.54  thf('50', plain,
% 3.36/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.36/3.54        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B))),
% 3.36/3.54      inference('sup-', [status(thm)], ['5', '49'])).
% 3.36/3.54  thf('51', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 3.36/3.54      inference('simplify', [status(thm)], ['50'])).
% 3.36/3.54  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 3.36/3.54  
% 3.36/3.54  % SZS output end Refutation
% 3.36/3.54  
% 3.36/3.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

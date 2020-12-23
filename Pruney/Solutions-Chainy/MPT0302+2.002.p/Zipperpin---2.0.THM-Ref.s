%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PkhXaiJNg4

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:05 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 139 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  571 (1049 expanded)
%              Number of equality atoms :   43 (  95 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ X18 @ X21 ) )
      | ~ ( r1_xboole_0 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('24',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','32'])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_xboole_0 @ X15 @ X17 )
      | ( X15 = X17 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_xboole_0 @ X22 @ X23 )
      | ( r2_hidden @ ( sk_C_2 @ X23 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['37','57'])).

thf('59',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PkhXaiJNg4
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.81/3.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.81/3.04  % Solved by: fo/fo7.sh
% 2.81/3.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.81/3.04  % done 4966 iterations in 2.592s
% 2.81/3.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.81/3.04  % SZS output start Refutation
% 2.81/3.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.81/3.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.81/3.04  thf(sk_B_type, type, sk_B: $i).
% 2.81/3.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.81/3.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.81/3.04  thf(sk_A_type, type, sk_A: $i).
% 2.81/3.04  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.81/3.04  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.81/3.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.81/3.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.81/3.04  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 2.81/3.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.81/3.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.81/3.04  thf(d3_tarski, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( r1_tarski @ A @ B ) <=>
% 2.81/3.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.81/3.04  thf('0', plain,
% 2.81/3.04      (![X3 : $i, X5 : $i]:
% 2.81/3.04         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.81/3.04      inference('cnf', [status(esa)], [d3_tarski])).
% 2.81/3.04  thf(t5_boole, axiom,
% 2.81/3.04    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.81/3.04  thf('1', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 2.81/3.04      inference('cnf', [status(esa)], [t5_boole])).
% 2.81/3.04  thf(l97_xboole_1, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 2.81/3.04  thf('2', plain,
% 2.81/3.04      (![X24 : $i, X25 : $i]:
% 2.81/3.04         (r1_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k5_xboole_0 @ X24 @ X25))),
% 2.81/3.04      inference('cnf', [status(esa)], [l97_xboole_1])).
% 2.81/3.04  thf('3', plain,
% 2.81/3.04      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 2.81/3.04      inference('sup+', [status(thm)], ['1', '2'])).
% 2.81/3.04  thf(d7_xboole_0, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.81/3.04       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.81/3.04  thf('4', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (((k3_xboole_0 @ X12 @ X13) = (k1_xboole_0))
% 2.81/3.04          | ~ (r1_xboole_0 @ X12 @ X13))),
% 2.81/3.04      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.81/3.04  thf('5', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.81/3.04  thf(commutativity_k3_xboole_0, axiom,
% 2.81/3.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.81/3.04  thf('6', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.81/3.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.81/3.04  thf('7', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 2.81/3.04      inference('demod', [status(thm)], ['5', '6'])).
% 2.81/3.04  thf('8', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.81/3.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.81/3.04  thf(t4_xboole_0, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.81/3.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.81/3.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.81/3.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.81/3.04  thf('9', plain,
% 2.81/3.04      (![X18 : $i, X20 : $i, X21 : $i]:
% 2.81/3.04         (~ (r2_hidden @ X20 @ (k3_xboole_0 @ X18 @ X21))
% 2.81/3.04          | ~ (r1_xboole_0 @ X18 @ X21))),
% 2.81/3.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.81/3.04  thf('10', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.04         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.81/3.04          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.81/3.04      inference('sup-', [status(thm)], ['8', '9'])).
% 2.81/3.04  thf('11', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 2.81/3.04          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['7', '10'])).
% 2.81/3.04  thf('12', plain,
% 2.81/3.04      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 2.81/3.04      inference('sup+', [status(thm)], ['1', '2'])).
% 2.81/3.04  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.81/3.04      inference('demod', [status(thm)], ['11', '12'])).
% 2.81/3.04  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.81/3.04      inference('sup-', [status(thm)], ['0', '13'])).
% 2.81/3.04  thf(t28_xboole_1, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.81/3.04  thf('15', plain,
% 2.81/3.04      (![X26 : $i, X27 : $i]:
% 2.81/3.04         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 2.81/3.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.81/3.04  thf('16', plain,
% 2.81/3.04      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['14', '15'])).
% 2.81/3.04  thf('17', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.81/3.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.81/3.04  thf('18', plain,
% 2.81/3.04      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.81/3.04      inference('sup+', [status(thm)], ['16', '17'])).
% 2.81/3.04  thf('19', plain,
% 2.81/3.04      (![X3 : $i, X5 : $i]:
% 2.81/3.04         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.81/3.04      inference('cnf', [status(esa)], [d3_tarski])).
% 2.81/3.04  thf('20', plain,
% 2.81/3.04      (![X3 : $i, X5 : $i]:
% 2.81/3.04         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.81/3.04      inference('cnf', [status(esa)], [d3_tarski])).
% 2.81/3.04  thf(l54_zfmisc_1, axiom,
% 2.81/3.04    (![A:$i,B:$i,C:$i,D:$i]:
% 2.81/3.04     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 2.81/3.04       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 2.81/3.04  thf('21', plain,
% 2.81/3.04      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 2.81/3.04         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 2.81/3.04          | ~ (r2_hidden @ X31 @ X33)
% 2.81/3.04          | ~ (r2_hidden @ X29 @ X30))),
% 2.81/3.04      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.81/3.04  thf('22', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.81/3.04         ((r1_tarski @ X0 @ X1)
% 2.81/3.04          | ~ (r2_hidden @ X3 @ X2)
% 2.81/3.04          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 2.81/3.04             (k2_zfmisc_1 @ X2 @ X0)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['20', '21'])).
% 2.81/3.04  thf('23', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.81/3.04         ((r1_tarski @ X0 @ X1)
% 2.81/3.04          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 2.81/3.04             (k2_zfmisc_1 @ X0 @ X2))
% 2.81/3.04          | (r1_tarski @ X2 @ X3))),
% 2.81/3.04      inference('sup-', [status(thm)], ['19', '22'])).
% 2.81/3.04  thf(t114_zfmisc_1, conjecture,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 2.81/3.04       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.81/3.04         ( ( A ) = ( B ) ) ) ))).
% 2.81/3.04  thf(zf_stmt_0, negated_conjecture,
% 2.81/3.04    (~( ![A:$i,B:$i]:
% 2.81/3.04        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 2.81/3.04          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.81/3.04            ( ( A ) = ( B ) ) ) ) )),
% 2.81/3.04    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 2.81/3.04  thf('24', plain,
% 2.81/3.04      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('25', plain,
% 2.81/3.04      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.81/3.04         ((r2_hidden @ X29 @ X30)
% 2.81/3.04          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 2.81/3.04      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.81/3.04  thf('26', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.81/3.04          | (r2_hidden @ X1 @ sk_B))),
% 2.81/3.04      inference('sup-', [status(thm)], ['24', '25'])).
% 2.81/3.04  thf('27', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         ((r1_tarski @ sk_B @ X0)
% 2.81/3.04          | (r1_tarski @ sk_A @ X1)
% 2.81/3.04          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 2.81/3.04      inference('sup-', [status(thm)], ['23', '26'])).
% 2.81/3.04  thf('28', plain,
% 2.81/3.04      (![X3 : $i, X5 : $i]:
% 2.81/3.04         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 2.81/3.04      inference('cnf', [status(esa)], [d3_tarski])).
% 2.81/3.04  thf('29', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ sk_A @ sk_B)
% 2.81/3.04          | (r1_tarski @ sk_B @ X0)
% 2.81/3.04          | (r1_tarski @ sk_A @ sk_B))),
% 2.81/3.04      inference('sup-', [status(thm)], ['27', '28'])).
% 2.81/3.04  thf('30', plain,
% 2.81/3.04      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ sk_B))),
% 2.81/3.04      inference('simplify', [status(thm)], ['29'])).
% 2.81/3.04  thf('31', plain,
% 2.81/3.04      (![X26 : $i, X27 : $i]:
% 2.81/3.04         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 2.81/3.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.81/3.04  thf('32', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ sk_A @ sk_B) | ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['30', '31'])).
% 2.81/3.04  thf('33', plain, ((((k1_xboole_0) = (sk_B)) | (r1_tarski @ sk_A @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['18', '32'])).
% 2.81/3.04  thf('34', plain, (((sk_B) != (k1_xboole_0))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('35', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.81/3.04      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 2.81/3.04  thf('36', plain,
% 2.81/3.04      (![X26 : $i, X27 : $i]:
% 2.81/3.04         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 2.81/3.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.81/3.04  thf('37', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.81/3.04      inference('sup-', [status(thm)], ['35', '36'])).
% 2.81/3.04  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.81/3.04      inference('sup-', [status(thm)], ['0', '13'])).
% 2.81/3.04  thf(d8_xboole_0, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( r2_xboole_0 @ A @ B ) <=>
% 2.81/3.04       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 2.81/3.04  thf('39', plain,
% 2.81/3.04      (![X15 : $i, X17 : $i]:
% 2.81/3.04         ((r2_xboole_0 @ X15 @ X17)
% 2.81/3.04          | ((X15) = (X17))
% 2.81/3.04          | ~ (r1_tarski @ X15 @ X17))),
% 2.81/3.04      inference('cnf', [status(esa)], [d8_xboole_0])).
% 2.81/3.04  thf('40', plain,
% 2.81/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['38', '39'])).
% 2.81/3.04  thf(t6_xboole_0, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 2.81/3.04          ( ![C:$i]:
% 2.81/3.04            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 2.81/3.04  thf('41', plain,
% 2.81/3.04      (![X22 : $i, X23 : $i]:
% 2.81/3.04         (~ (r2_xboole_0 @ X22 @ X23)
% 2.81/3.04          | (r2_hidden @ (sk_C_2 @ X23 @ X22) @ X23))),
% 2.81/3.04      inference('cnf', [status(esa)], [t6_xboole_0])).
% 2.81/3.04  thf('42', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k1_xboole_0) = (X0))
% 2.81/3.04          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['40', '41'])).
% 2.81/3.04  thf('43', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.81/3.04         ((r1_tarski @ X0 @ X1)
% 2.81/3.04          | ~ (r2_hidden @ X3 @ X2)
% 2.81/3.04          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 2.81/3.04             (k2_zfmisc_1 @ X2 @ X0)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['20', '21'])).
% 2.81/3.04  thf('44', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.04         (((k1_xboole_0) = (X0))
% 2.81/3.04          | (r2_hidden @ 
% 2.81/3.04             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 2.81/3.04             (k2_zfmisc_1 @ X0 @ X1))
% 2.81/3.04          | (r1_tarski @ X1 @ X2))),
% 2.81/3.04      inference('sup-', [status(thm)], ['42', '43'])).
% 2.81/3.04  thf('45', plain,
% 2.81/3.04      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('46', plain,
% 2.81/3.04      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.81/3.04         ((r2_hidden @ X31 @ X32)
% 2.81/3.04          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 2.81/3.04      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.81/3.04  thf('47', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.81/3.04          | (r2_hidden @ X0 @ sk_A))),
% 2.81/3.04      inference('sup-', [status(thm)], ['45', '46'])).
% 2.81/3.04  thf('48', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ sk_B @ X0)
% 2.81/3.04          | ((k1_xboole_0) = (sk_A))
% 2.81/3.04          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 2.81/3.04      inference('sup-', [status(thm)], ['44', '47'])).
% 2.81/3.04  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('50', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 2.81/3.04      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 2.81/3.04  thf('51', plain,
% 2.81/3.04      (![X3 : $i, X5 : $i]:
% 2.81/3.04         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 2.81/3.04      inference('cnf', [status(esa)], [d3_tarski])).
% 2.81/3.04  thf('52', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 2.81/3.04      inference('sup-', [status(thm)], ['50', '51'])).
% 2.81/3.04  thf('53', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.81/3.04      inference('simplify', [status(thm)], ['52'])).
% 2.81/3.04  thf('54', plain,
% 2.81/3.04      (![X26 : $i, X27 : $i]:
% 2.81/3.04         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 2.81/3.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.81/3.04  thf('55', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.81/3.04      inference('sup-', [status(thm)], ['53', '54'])).
% 2.81/3.04  thf('56', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.81/3.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.81/3.04  thf('57', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['55', '56'])).
% 2.81/3.04  thf('58', plain, (((sk_A) = (sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['37', '57'])).
% 2.81/3.04  thf('59', plain, (((sk_A) != (sk_B))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('60', plain, ($false),
% 2.81/3.04      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 2.81/3.04  
% 2.81/3.04  % SZS output end Refutation
% 2.81/3.04  
% 2.81/3.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

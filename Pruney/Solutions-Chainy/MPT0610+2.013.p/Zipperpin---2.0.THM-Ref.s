%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3AItx54LxW

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:06 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 121 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   20
%              Number of atoms          :  573 (1044 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t214_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t214_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X19 @ X18 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X19 @ X18 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

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

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k9_relat_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,
    ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('38',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','40','41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','43'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3AItx54LxW
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 176 iterations in 0.139s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.60  thf(t214_relat_1, conjecture,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( v1_relat_1 @ B ) =>
% 0.39/0.60           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.60             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i]:
% 0.39/0.60        ( ( v1_relat_1 @ A ) =>
% 0.39/0.60          ( ![B:$i]:
% 0.39/0.60            ( ( v1_relat_1 @ B ) =>
% 0.39/0.60              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.60                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 0.39/0.60  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(fc1_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.39/0.60  thf('2', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(d7_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.39/0.60         = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf(t14_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( v1_relat_1 @ B ) =>
% 0.39/0.60           ( r1_tarski @
% 0.39/0.60             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.39/0.60             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X18 : $i, X19 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X18)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X19 @ X18)) @ 
% 0.39/0.60             (k3_xboole_0 @ (k1_relat_1 @ X19) @ (k1_relat_1 @ X18)))
% 0.39/0.60          | ~ (v1_relat_1 @ X19))),
% 0.39/0.60      inference('cnf', [status(esa)], [t14_relat_1])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)
% 0.39/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.39/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)),
% 0.39/0.60      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.39/0.60         = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      (![X18 : $i, X19 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X18)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X19 @ X18)) @ 
% 0.39/0.60             (k3_xboole_0 @ (k1_relat_1 @ X19) @ (k1_relat_1 @ X18)))
% 0.39/0.60          | ~ (v1_relat_1 @ X19))),
% 0.39/0.60      inference('cnf', [status(esa)], [t14_relat_1])).
% 0.39/0.60  thf(t67_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.39/0.60         ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.60       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         (((X9) = (k1_xboole_0))
% 0.39/0.60          | ~ (r1_tarski @ X9 @ X10)
% 0.39/0.60          | ~ (r1_tarski @ X9 @ X11)
% 0.39/0.60          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.39/0.60      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X1)
% 0.39/0.60          | ~ (v1_relat_1 @ X0)
% 0.39/0.60          | ~ (r1_xboole_0 @ 
% 0.39/0.60               (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)) @ X2)
% 0.39/0.60          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.39/0.60          | ((k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.60          | ((k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.39/0.60          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)
% 0.39/0.60          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.60          | ~ (v1_relat_1 @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['10', '13'])).
% 0.39/0.60  thf(t3_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X5 : $i, X6 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.60  thf('16', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t151_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (r1_xboole_0 @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.60          | ((k9_relat_1 @ X20 @ X21) = (k1_xboole_0))
% 0.39/0.60          | ~ (v1_relat_1 @ X20))),
% 0.39/0.60      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_A)
% 0.39/0.60        | ((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.60  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf(t143_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ C ) =>
% 0.39/0.60       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.39/0.60         ( ?[D:$i]:
% 0.39/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.39/0.60             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.39/0.60             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.39/0.60          | (r2_hidden @ (sk_D @ X17 @ X15 @ X16) @ (k1_relat_1 @ X17))
% 0.39/0.60          | ~ (v1_relat_1 @ X17))),
% 0.39/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_relat_1 @ sk_A)
% 0.39/0.60          | (r2_hidden @ (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ X0) @ 
% 0.39/0.60             (k1_relat_1 @ sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.60  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.60          | (r2_hidden @ (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ X0) @ 
% 0.39/0.60             (k1_relat_1 @ sk_A)))),
% 0.39/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.60  thf('25', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.60          | (r2_hidden @ 
% 0.39/0.60             (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 0.39/0.60             (k1_relat_1 @ sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['15', '24'])).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      (![X5 : $i, X6 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      (((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf('28', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.39/0.60          | (r2_hidden @ (sk_D @ X17 @ X15 @ X16) @ X15)
% 0.39/0.60          | ~ (v1_relat_1 @ X17))),
% 0.39/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_relat_1 @ sk_A)
% 0.39/0.60          | (r2_hidden @ (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ X0) @ 
% 0.39/0.60             (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.60          | (r2_hidden @ (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ X0) @ 
% 0.39/0.60             (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.60          | (r2_hidden @ 
% 0.39/0.60             (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 0.39/0.60             (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['26', '31'])).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X7 @ X5)
% 0.39/0.60          | ~ (r2_hidden @ X7 @ X8)
% 0.39/0.60          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.60          | ~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X1)
% 0.39/0.60          | ~ (r2_hidden @ 
% 0.39/0.60               (sk_D @ sk_A @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 0.39/0.60               X1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.60          | ~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.39/0.60          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['25', '34'])).
% 0.39/0.60  thf('36', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.60  thf('38', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['35', '38'])).
% 0.39/0.60  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.39/0.60      inference('simplify', [status(thm)], ['39'])).
% 0.39/0.60  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('43', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.39/0.60          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['14', '40', '41', '42'])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (((k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['9', '43'])).
% 0.39/0.60  thf(t64_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('45', plain,
% 0.39/0.60      (![X22 : $i]:
% 0.39/0.60         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.39/0.60          | ((X22) = (k1_xboole_0))
% 0.39/0.60          | ~ (v1_relat_1 @ X22))),
% 0.39/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.39/0.60  thf('46', plain,
% 0.39/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.39/0.60        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.60  thf('47', plain,
% 0.39/0.60      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.39/0.60        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.60  thf('48', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['1', '47'])).
% 0.39/0.60  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('50', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.60  thf('51', plain,
% 0.39/0.60      (![X0 : $i, X2 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.60  thf('53', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.39/0.60      inference('simplify', [status(thm)], ['52'])).
% 0.39/0.60  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pgJUcpI8yq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:49 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 119 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  544 ( 794 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t30_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_ordinal1])).

thf('0',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ ( k3_tarski @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ~ ( r1_tarski @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( ( k3_tarski @ X0 )
        = X0 )
      | ( r2_xboole_0 @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r2_hidden @ X18 @ X17 )
      | ~ ( r2_xboole_0 @ X18 @ X17 )
      | ~ ( v1_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( ( k3_tarski @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k3_tarski @ X0 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( ( k3_tarski @ X0 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( ( k3_tarski @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X10 @ X11 )
      | ( r1_ordinal1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ~ ( r1_tarski @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('40',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ ( sk_B @ sk_A ) )
    | ( v1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_ordinal1 @ sk_A @ ( sk_B @ sk_A ) )
    | ( v1_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('46',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( sk_B @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( sk_B @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( v1_ordinal1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_ordinal1 @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k3_tarski @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['26','56','57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pgJUcpI8yq
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:21:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 190 iterations in 0.152s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.62  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.62  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.43/0.62  thf(t30_ordinal1, conjecture,
% 0.43/0.62    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.43/0.62  thf('0', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d2_ordinal1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_ordinal1 @ A ) <=>
% 0.43/0.62       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X14 : $i]: ((v1_ordinal1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.43/0.62  thf(t94_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.43/0.62       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i]:
% 0.43/0.62         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.43/0.62          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X12 @ X13)
% 0.43/0.62          | (r1_tarski @ X12 @ X13)
% 0.43/0.62          | ~ (v1_ordinal1 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.43/0.62          | ~ (v1_ordinal1 @ X0)
% 0.43/0.62          | (r1_tarski @ (sk_C @ X1 @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i]:
% 0.43/0.62         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.43/0.62          | ~ (r1_tarski @ (sk_C @ X4 @ X3) @ X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_ordinal1 @ X0)
% 0.43/0.62          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.43/0.62          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.62  thf(t95_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) =>
% 0.43/0.62       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]:
% 0.43/0.62         ((r1_tarski @ (k3_tarski @ X5) @ (k3_tarski @ X6))
% 0.43/0.62          | ~ (r1_tarski @ X5 @ X6))),
% 0.43/0.62      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_ordinal1 @ X0)
% 0.43/0.62          | (r1_tarski @ (k3_tarski @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf(t56_setfam_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.43/0.62       ( r1_tarski @ C @ B ) ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k3_tarski @ X7) @ X8)
% 0.43/0.62          | ~ (r2_hidden @ X9 @ X7)
% 0.43/0.62          | (r1_tarski @ X9 @ X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_ordinal1 @ X0)
% 0.43/0.62          | (r1_tarski @ X1 @ (k3_tarski @ X0))
% 0.43/0.62          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.43/0.62          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0))
% 0.43/0.62          | ~ (v1_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X14 : $i]: ((v1_ordinal1 @ X14) | ~ (r1_tarski @ (sk_B @ X14) @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i]: (~ (v1_ordinal1 @ X0) | (v1_ordinal1 @ (k3_tarski @ X0)))),
% 0.43/0.62      inference('clc', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.62  thf(d8_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.43/0.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i, X2 : $i]:
% 0.43/0.62         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_ordinal1 @ X0)
% 0.43/0.62          | ((k3_tarski @ X0) = (X0))
% 0.43/0.62          | (r2_xboole_0 @ (k3_tarski @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf(t21_ordinal1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_ordinal1 @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.43/0.62           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X17)
% 0.43/0.62          | (r2_hidden @ X18 @ X17)
% 0.43/0.62          | ~ (r2_xboole_0 @ X18 @ X17)
% 0.43/0.62          | ~ (v1_ordinal1 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k3_tarski @ X0) = (X0))
% 0.43/0.62          | ~ (v1_ordinal1 @ X0)
% 0.43/0.62          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.43/0.62          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_ordinal1 @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.43/0.62          | ~ (v1_ordinal1 @ X0)
% 0.43/0.62          | ((k3_tarski @ X0) = (X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['14', '19'])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k3_tarski @ X0) = (X0))
% 0.43/0.62          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | ~ (v1_ordinal1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['20'])).
% 0.43/0.62  thf(t23_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]:
% 0.43/0.62         ((v3_ordinal1 @ X19)
% 0.43/0.62          | ~ (v3_ordinal1 @ X20)
% 0.43/0.62          | ~ (r2_hidden @ X19 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_ordinal1 @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | ((k3_tarski @ X0) = (X0))
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.43/0.62          | ((k3_tarski @ X0) = (X0))
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | ~ (v1_ordinal1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.43/0.62  thf('25', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      ((~ (v1_ordinal1 @ sk_A)
% 0.43/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.43/0.62        | ((k3_tarski @ sk_A) = (sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X14 : $i]: ((v1_ordinal1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]:
% 0.43/0.62         ((v3_ordinal1 @ X19)
% 0.43/0.62          | ~ (v3_ordinal1 @ X20)
% 0.43/0.62          | ~ (r2_hidden @ X19 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_ordinal1 @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (v3_ordinal1 @ (sk_B @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_ordinal1 @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (v3_ordinal1 @ (sk_B @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(connectedness_r1_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.43/0.62       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X10)
% 0.43/0.62          | ~ (v3_ordinal1 @ X11)
% 0.43/0.62          | (r1_ordinal1 @ X10 @ X11)
% 0.43/0.62          | (r1_ordinal1 @ X11 @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_ordinal1 @ X0 @ sk_A)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf(redefinition_r1_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.43/0.62       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X15 : $i, X16 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X15)
% 0.43/0.62          | ~ (v3_ordinal1 @ X16)
% 0.43/0.62          | (r1_tarski @ X15 @ X16)
% 0.43/0.62          | ~ (r1_ordinal1 @ X15 @ X16))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.43/0.62          | ~ (v3_ordinal1 @ sk_A)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ sk_A)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X14 : $i]: ((v1_ordinal1 @ X14) | ~ (r1_tarski @ (sk_B @ X14) @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      ((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.43/0.62        | (r1_ordinal1 @ sk_A @ (sk_B @ sk_A))
% 0.43/0.62        | (v1_ordinal1 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.43/0.62        | (v1_ordinal1 @ sk_A)
% 0.43/0.62        | (v1_ordinal1 @ sk_A)
% 0.43/0.62        | (r1_ordinal1 @ sk_A @ (sk_B @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['30', '40'])).
% 0.43/0.62  thf('42', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (((v1_ordinal1 @ sk_A)
% 0.43/0.62        | (v1_ordinal1 @ sk_A)
% 0.43/0.62        | (r1_ordinal1 @ sk_A @ (sk_B @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((r1_ordinal1 @ sk_A @ (sk_B @ sk_A)) | (v1_ordinal1 @ sk_A))),
% 0.43/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X15 : $i, X16 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X15)
% 0.43/0.62          | ~ (v3_ordinal1 @ X16)
% 0.43/0.62          | (r1_tarski @ X15 @ X16)
% 0.43/0.62          | ~ (r1_ordinal1 @ X15 @ X16))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (((v1_ordinal1 @ sk_A)
% 0.43/0.62        | (r1_tarski @ sk_A @ (sk_B @ sk_A))
% 0.43/0.62        | ~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.43/0.62        | ~ (v3_ordinal1 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (((v1_ordinal1 @ sk_A)
% 0.43/0.62        | (r1_tarski @ sk_A @ (sk_B @ sk_A))
% 0.43/0.62        | ~ (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X14 : $i]: ((v1_ordinal1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.43/0.62  thf(t7_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf('52', plain, ((~ (v3_ordinal1 @ (sk_B @ sk_A)) | (v1_ordinal1 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['48', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      ((~ (v3_ordinal1 @ sk_A) | (v1_ordinal1 @ sk_A) | (v1_ordinal1 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '52'])).
% 0.43/0.62  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('55', plain, (((v1_ordinal1 @ sk_A) | (v1_ordinal1 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('56', plain, ((v1_ordinal1 @ sk_A)),
% 0.43/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.43/0.62  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('58', plain, (((k3_tarski @ sk_A) = (sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['26', '56', '57'])).
% 0.43/0.62  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('60', plain, ($false),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '58', '59'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

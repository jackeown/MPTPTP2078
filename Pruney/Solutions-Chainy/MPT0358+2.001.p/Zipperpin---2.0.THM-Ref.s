%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3vuOi51h6o

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:21 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 137 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  510 (1170 expanded)
%              Number of equality atoms :   56 ( 126 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k1_subset_1 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('13',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('18',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','19','20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','41'])).

thf('43',plain,(
    ! [X16: $i] :
      ( ( k1_subset_1 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('44',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','19'])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3vuOi51h6o
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.68  % Solved by: fo/fo7.sh
% 1.51/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.68  % done 1603 iterations in 1.223s
% 1.51/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.68  % SZS output start Refutation
% 1.51/1.68  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.51/1.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.51/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.51/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.68  thf(t38_subset_1, conjecture,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.68       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 1.51/1.68         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 1.51/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.68    (~( ![A:$i,B:$i]:
% 1.51/1.68        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.68          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 1.51/1.68            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 1.51/1.68    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 1.51/1.68  thf('0', plain,
% 1.51/1.68      ((((sk_B) = (k1_subset_1 @ sk_A))
% 1.51/1.68        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.51/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.68  thf('1', plain,
% 1.51/1.68      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.51/1.68         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.51/1.68      inference('split', [status(esa)], ['0'])).
% 1.51/1.68  thf('2', plain,
% 1.51/1.68      ((((sk_B) != (k1_subset_1 @ sk_A))
% 1.51/1.68        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.51/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.68  thf('3', plain,
% 1.51/1.68      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 1.51/1.68       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.51/1.68      inference('split', [status(esa)], ['2'])).
% 1.51/1.68  thf(commutativity_k2_xboole_0, axiom,
% 1.51/1.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.51/1.68  thf('4', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.68  thf(t1_boole, axiom,
% 1.51/1.68    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.51/1.68  thf('5', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.51/1.68      inference('cnf', [status(esa)], [t1_boole])).
% 1.51/1.68  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.51/1.68      inference('sup+', [status(thm)], ['4', '5'])).
% 1.51/1.68  thf(t46_xboole_1, axiom,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.51/1.68  thf('7', plain,
% 1.51/1.68      (![X14 : $i, X15 : $i]:
% 1.51/1.68         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 1.51/1.68      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.51/1.68  thf('8', plain,
% 1.51/1.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.51/1.68      inference('sup+', [status(thm)], ['6', '7'])).
% 1.51/1.68  thf(l32_xboole_1, axiom,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.68  thf('9', plain,
% 1.51/1.68      (![X8 : $i, X9 : $i]:
% 1.51/1.68         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 1.51/1.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.51/1.68  thf('10', plain,
% 1.51/1.68      (![X0 : $i]:
% 1.51/1.68         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.51/1.68      inference('sup-', [status(thm)], ['8', '9'])).
% 1.51/1.68  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.51/1.68      inference('simplify', [status(thm)], ['10'])).
% 1.51/1.68  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.51/1.68  thf('12', plain, (![X16 : $i]: ((k1_subset_1 @ X16) = (k1_xboole_0))),
% 1.51/1.68      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.51/1.68  thf('13', plain,
% 1.51/1.68      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('split', [status(esa)], ['0'])).
% 1.51/1.68  thf('14', plain,
% 1.51/1.68      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('sup+', [status(thm)], ['12', '13'])).
% 1.51/1.68  thf('15', plain,
% 1.51/1.68      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.51/1.68         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.51/1.68      inference('split', [status(esa)], ['2'])).
% 1.51/1.68  thf('16', plain,
% 1.51/1.68      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 1.51/1.68         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 1.51/1.68             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('sup-', [status(thm)], ['14', '15'])).
% 1.51/1.68  thf('17', plain,
% 1.51/1.68      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('sup+', [status(thm)], ['12', '13'])).
% 1.51/1.68  thf('18', plain,
% 1.51/1.68      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 1.51/1.68         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 1.51/1.68             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('demod', [status(thm)], ['16', '17'])).
% 1.51/1.68  thf('19', plain,
% 1.51/1.68      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 1.51/1.68       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 1.51/1.68      inference('sup-', [status(thm)], ['11', '18'])).
% 1.51/1.68  thf('20', plain,
% 1.51/1.68      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 1.51/1.68       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 1.51/1.68      inference('split', [status(esa)], ['0'])).
% 1.51/1.68  thf('21', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.51/1.68      inference('sat_resolution*', [status(thm)], ['3', '19', '20'])).
% 1.51/1.68  thf('22', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.51/1.68      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 1.51/1.68  thf('23', plain,
% 1.51/1.68      (![X8 : $i, X10 : $i]:
% 1.51/1.68         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 1.51/1.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.51/1.68  thf('24', plain,
% 1.51/1.68      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.51/1.68      inference('sup-', [status(thm)], ['22', '23'])).
% 1.51/1.68  thf(d5_xboole_0, axiom,
% 1.51/1.68    (![A:$i,B:$i,C:$i]:
% 1.51/1.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.51/1.68       ( ![D:$i]:
% 1.51/1.68         ( ( r2_hidden @ D @ C ) <=>
% 1.51/1.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.51/1.68  thf('25', plain,
% 1.51/1.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.51/1.68         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.51/1.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.51/1.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.51/1.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.51/1.68  thf('26', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.51/1.68      inference('eq_fact', [status(thm)], ['25'])).
% 1.51/1.68  thf('27', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.51/1.68      inference('eq_fact', [status(thm)], ['25'])).
% 1.51/1.68  thf('28', plain,
% 1.51/1.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.51/1.68         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.51/1.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.51/1.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.51/1.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.51/1.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.51/1.68  thf('29', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.51/1.68          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.68          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.51/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.51/1.68      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.68  thf('30', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.51/1.68          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.51/1.68      inference('simplify', [status(thm)], ['29'])).
% 1.51/1.68  thf('31', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.51/1.68      inference('eq_fact', [status(thm)], ['25'])).
% 1.51/1.68  thf('32', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.51/1.68          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.51/1.68      inference('clc', [status(thm)], ['30', '31'])).
% 1.51/1.68  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.51/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.68  thf(d5_subset_1, axiom,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.51/1.68  thf('34', plain,
% 1.51/1.68      (![X17 : $i, X18 : $i]:
% 1.51/1.68         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.51/1.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.51/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.51/1.68  thf('35', plain,
% 1.51/1.68      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.51/1.68      inference('sup-', [status(thm)], ['33', '34'])).
% 1.51/1.68  thf('36', plain,
% 1.51/1.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.51/1.68         (~ (r2_hidden @ X6 @ X5)
% 1.51/1.68          | ~ (r2_hidden @ X6 @ X4)
% 1.51/1.68          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.51/1.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.51/1.68  thf('37', plain,
% 1.51/1.68      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.51/1.68         (~ (r2_hidden @ X6 @ X4)
% 1.51/1.68          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.51/1.68      inference('simplify', [status(thm)], ['36'])).
% 1.51/1.68  thf('38', plain,
% 1.51/1.68      (![X0 : $i]:
% 1.51/1.68         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 1.51/1.68          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.51/1.68      inference('sup-', [status(thm)], ['35', '37'])).
% 1.51/1.68  thf('39', plain,
% 1.51/1.68      (![X0 : $i]:
% 1.51/1.68         (((X0) = (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.51/1.68          | ~ (r2_hidden @ (sk_D @ X0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0) @ 
% 1.51/1.68               sk_B))),
% 1.51/1.68      inference('sup-', [status(thm)], ['32', '38'])).
% 1.51/1.68  thf('40', plain,
% 1.51/1.68      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.51/1.68        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.51/1.68      inference('sup-', [status(thm)], ['26', '39'])).
% 1.51/1.68  thf('41', plain,
% 1.51/1.68      (((sk_B) = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.51/1.68      inference('simplify', [status(thm)], ['40'])).
% 1.51/1.68  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 1.51/1.68      inference('sup+', [status(thm)], ['24', '41'])).
% 1.51/1.68  thf('43', plain, (![X16 : $i]: ((k1_subset_1 @ X16) = (k1_xboole_0))),
% 1.51/1.68      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.51/1.68  thf('44', plain,
% 1.51/1.68      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 1.51/1.68         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('split', [status(esa)], ['2'])).
% 1.51/1.68  thf('45', plain,
% 1.51/1.68      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 1.51/1.68      inference('sup-', [status(thm)], ['43', '44'])).
% 1.51/1.68  thf('46', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 1.51/1.68      inference('sat_resolution*', [status(thm)], ['3', '19'])).
% 1.51/1.68  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 1.51/1.68      inference('simpl_trail', [status(thm)], ['45', '46'])).
% 1.51/1.68  thf('48', plain, ($false),
% 1.51/1.68      inference('simplify_reflect-', [status(thm)], ['42', '47'])).
% 1.51/1.68  
% 1.51/1.68  % SZS output end Refutation
% 1.51/1.68  
% 1.51/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

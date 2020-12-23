%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjJjQWpNU7

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:37 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  486 ( 935 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t92_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k3_tarski @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_C_1 )
      | ( r2_hidden @ X22 @ sk_B )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simplify,[status(thm)],['28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( sk_B = sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k3_tarski @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( r2_hidden @ X22 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['33','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjJjQWpNU7
% 0.15/0.36  % Computer   : n001.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:56:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 233 iterations in 0.118s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.58  thf(d3_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf(t8_subset_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ![C:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58           ( ( ![D:$i]:
% 0.37/0.58               ( ( m1_subset_1 @ D @ A ) =>
% 0.37/0.58                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.37/0.58             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i]:
% 0.37/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58          ( ![C:$i]:
% 0.37/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58              ( ( ![D:$i]:
% 0.37/0.58                  ( ( m1_subset_1 @ D @ A ) =>
% 0.37/0.58                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.37/0.58                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.37/0.58  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d2_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.37/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.37/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X19 @ X20)
% 0.37/0.58          | (r2_hidden @ X19 @ X20)
% 0.37/0.58          | (v1_xboole_0 @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.58        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf(t92_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i]:
% 0.37/0.58         ((r1_tarski @ X16 @ (k3_tarski @ X17)) | ~ (r2_hidden @ X16 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [t92_zfmisc_1])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.58        | (r1_tarski @ sk_C_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf(t99_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.37/0.58  thf('6', plain, (![X18 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X18)) = (X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X21 @ X20)
% 0.37/0.58          | (v1_xboole_0 @ X21)
% 0.37/0.58          | ~ (v1_xboole_0 @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain, (((r1_tarski @ sk_C_1 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf(t7_boole, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X12 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_boole])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.58  thf('15', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.37/0.58      inference('clc', [status(thm)], ['11', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.58          | (r2_hidden @ X0 @ X2)
% 0.37/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '17'])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X19 @ X20)
% 0.41/0.58          | (m1_subset_1 @ X19 @ X20)
% 0.41/0.58          | (v1_xboole_0 @ X20))),
% 0.41/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.58  thf('20', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X12 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.41/0.58      inference('cnf', [status(esa)], [t7_boole])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.41/0.58      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r1_tarski @ sk_C_1 @ X0)
% 0.41/0.58          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['18', '21'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X22 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X22 @ sk_C_1)
% 0.41/0.58          | (r2_hidden @ X22 @ sk_B)
% 0.41/0.58          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r1_tarski @ sk_C_1 @ X0)
% 0.41/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.41/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B) | (r1_tarski @ sk_C_1 @ X0))),
% 0.41/0.58      inference('clc', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (((r1_tarski @ sk_C_1 @ sk_B) | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.58  thf('29', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.41/0.58      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.58  thf(d10_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      (![X8 : $i, X10 : $i]:
% 0.41/0.58         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.41/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.58  thf('31', plain, ((~ (r1_tarski @ sk_B @ sk_C_1) | ((sk_B) = (sk_C_1)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.58  thf('32', plain, (((sk_B) != (sk_C_1))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('33', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X19 @ X20)
% 0.41/0.58          | (r2_hidden @ X19 @ X20)
% 0.41/0.58          | (v1_xboole_0 @ X20))),
% 0.41/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.58        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.58  thf('38', plain,
% 0.41/0.58      (![X16 : $i, X17 : $i]:
% 0.41/0.58         ((r1_tarski @ X16 @ (k3_tarski @ X17)) | ~ (r2_hidden @ X16 @ X17))),
% 0.41/0.58      inference('cnf', [status(esa)], [t92_zfmisc_1])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.58        | (r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.58  thf('40', plain, (![X18 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X18)) = (X18))),
% 0.41/0.58      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.58  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      (![X20 : $i, X21 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X21 @ X20)
% 0.41/0.58          | (v1_xboole_0 @ X21)
% 0.41/0.58          | ~ (v1_xboole_0 @ X20))),
% 0.41/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.58  thf('45', plain, (((r1_tarski @ sk_B @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['41', '44'])).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.58  thf('47', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.41/0.58      inference('clc', [status(thm)], ['45', '46'])).
% 0.41/0.58  thf('48', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.58          | (r2_hidden @ X0 @ X2)
% 0.41/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('49', plain,
% 0.41/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.58  thf('50', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['34', '49'])).
% 0.41/0.58  thf('51', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.41/0.58      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.58  thf('52', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r1_tarski @ sk_B @ X0) | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.58  thf('53', plain,
% 0.41/0.58      (![X22 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X22 @ sk_B)
% 0.41/0.58          | (r2_hidden @ X22 @ sk_C_1)
% 0.41/0.58          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('54', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r1_tarski @ sk_B @ X0)
% 0.41/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1)
% 0.41/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.58  thf('55', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('56', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1) | (r1_tarski @ sk_B @ X0))),
% 0.41/0.58      inference('clc', [status(thm)], ['54', '55'])).
% 0.41/0.58  thf('57', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('58', plain,
% 0.41/0.58      (((r1_tarski @ sk_B @ sk_C_1) | (r1_tarski @ sk_B @ sk_C_1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.58  thf('59', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.41/0.58      inference('simplify', [status(thm)], ['58'])).
% 0.41/0.58  thf('60', plain, ($false), inference('demod', [status(thm)], ['33', '59'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
